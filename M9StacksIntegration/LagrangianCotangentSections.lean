module

public import M9StacksIntegration.LagrangianCotangentMap
public import M9StacksIntegration.LagrangianPluckerQuotient
public import M9StacksIntegration.LagrangianSymplecticAction
public import M9StacksIntegration.SymmetricSquareLocalSections

/-! Exact section formulas for the native cotangent map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators TensorProduct

universe u

namespace M9Native.LagrangianCotangentSections

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianLocalPairing LagrangianCotangentMap
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X S : Scheme.{u}} {Q : X.Modules}

/-- The canonical sheafification unit into the literal native symmetric
square, read over the original ring of functions. -/
def squareUnit (F : X.Modules) (U : X.Opens) :
    SymPow.symmetricPower 2 Γ(X,U) Γ(F,U) →ₗ[Γ(X,U)] Γ(symmetricSquare F,U) :=
  ((PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
    (PresheafOfModules.symPowInt (O := X.sheaf.obj) 2 F.val)).app (op U)).hom

/-- The actual global map has exactly the original sectionwise formula
on the canonical unit. This is the sheafification adjunction, not an
independently imposed formula. -/
theorem cotangentMap_squareUnit (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (U : X.Opens)
    (x : SymPow.symmetricPower 2 Γ(X,U) Γ(dualSheaf Q,U)) :
    (cotangentMap p q hq).app U (squareUnit (dualSheaf Q) U x)=
      localSquareMap p q hq U x := by
  have h := congrArg (fun φ => φ.app (op U) x) (cotangentMap_sheafification p q hq)
  exact h

theorem cotangentMap_squareUnit_product (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (U : X.Opens) (α β : Γ(dualSheaf Q,U)) :
    (cotangentMap p q hq).app U
      (squareUnit (dualSheaf Q) U (SymPow.sqMul LinearMap.id (α ⊗ₜ[Γ(X,U)] β)))=
      localPairing p q hq U α β := by
  rw [cotangentMap_squareUnit,localSquareMap_product]

/-- On a genuine finite-free trivializing open the canonical unit of
the literal native symmetric square is bijective on every smaller open. -/
theorem squareUnit_bijective_of_iso_free (F : X.Modules) (W U : X.Opens) (h : U≤W)
    (I : Type u) [Finite I]
    (e : F.over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I) :
    Function.Bijective (squareUnit F U) := by
  have hs := SymmetricSquareBundleDeterminant.isSheaf_symPow_over_of_iso_free F W 2 I e
  have hsi : Presheaf.IsSheaf ((Opens.grothendieckTopology (X : TopCat)).over W)
      ((Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor X.ringCatSheaf W).obj
        (PresheafOfModules.symPowInt (O := X.sheaf.obj) 2 F.val)).presheaf := hs
  exact SymmetricSquareBundleDeterminant.bijective_unit_app_of_isSheaf_over X.ringCatSheaf W
    _ hsi (op (Over.mk (homOfLE h)))

/-- A verified local coefficient formula suffices to test the actual
global map on sections; no comparison-isomorphism premise is required. -/
theorem cotangentMap_app_bijective_of_localSquareMap (p : X ⟶ S)
    (q : freeOn X 6 ⟶ Q) (hq : AnnihilatesSigma X q)
    (W U : X.Opens) (h : U≤W) (I : Type u) [Finite I]
    (e : (dualSheaf Q).over W ≅ SheafOfModules.free (R := X.ringCatSheaf.over W) I)
    (hl : Function.Bijective (localSquareMap p q hq U)) :
    Function.Bijective ((cotangentMap p q hq).app U) := by
  have hu := squareUnit_bijective_of_iso_free (dualSheaf Q) W U h I e
  constructor
  · intro a b hab
    obtain ⟨x,rfl⟩ := hu.surjective a
    obtain ⟨y,rfl⟩ := hu.surjective b
    rw [cotangentMap_squareUnit,cotangentMap_squareUnit] at hab
    exact congrArg (squareUnit (dualSheaf Q) U) (hl.injective hab)
  · intro y
    obtain ⟨x,hx⟩ := hl.surjective y
    exact ⟨squareUnit (dualSheaf Q) U x,(cotangentMap_squareUnit p q hq U x).trans hx⟩

/-- The intrinsic map for the actual universal quotient of the frozen
native LG scheme. Its defining isotropy is proved from that zero scheme. -/
def universalCotangentMap (K : Type u) [Field K] :
    symmetricSquare (dualSheaf (LagrangianPluckerQuotient.quotientOnLG K).target) ⟶
      Scheme.Hom.relativeDifferentials (projection K) :=
  cotangentMap (projection K) (LagrangianPluckerQuotient.quotientOnLG K).map
    (LagrangianSymplecticAction.lagrangianUniversal_annihilates K)

end M9Native.LagrangianCotangentSections

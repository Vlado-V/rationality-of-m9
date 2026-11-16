module

public import M9StacksIntegration.LagrangianPluckerGeneration
public import M9StacksIntegration.LineFramePullback
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.FirstArrowStalk

/-! The actual projective chart functions multiply the original
determinant coordinates, in any actual pulled-back determinant frame. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.LagrangianProjectiveRatio

open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned
open Stacks.SectionsToProjectiveSpace
open Stacks.ProjectiveFromSections
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianPluckerGeneration

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Euler chart function and the original projective-space-moduli
fraction are the same native section, not merely equal at closed points. -/
theorem chartFracSection_eq_away (n : ℕ) (i j : Fin (n+1)) :
    chartFracSection (ULift.{u} ℤ) n i j =
      (AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
        (coordFrac.{u} i j) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [chartFracSection_val]
  change Localization.mk (MvPolynomial.X j : coordRing.{u} n) ⟨MvPolynomial.X i,_⟩ =
    Localization.mk (MvPolynomial.X j : coordRing.{u} n) ⟨(MvPolynomial.X i)^1,_⟩
  simp only [pow_one]

section NativeProjective

variable {T : Scheme.{u}} {n : ℕ} (h : T ⟶ projectiveSpaceAtUniverse.{u} n)
variable (e : (Scheme.Modules.pullback h).obj (twistingSheafAtUniverse.{u} n) ≅
  SheafOfModules.unit T.ringCatSheaf)

/-- Genuine O(1) chart relation after an arbitrary actual line frame.
It uses the original chart ring map and the original pulled sections. -/
theorem framed_ratio_product (i j : Fin (n+1)) :
    let D := ProjectiveSpectrum.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)
    let U := h ⁻¹ᵁ D
    (h.app D).hom (chartFracSection (ULift.{u} ℤ) n i j) *
        (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((e.hom.app ⊤ (pullbackCoordSection h i) : Γ(T,⊤))) =
      (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        ((e.hom.app ⊤ (pullbackCoordSection h j) : Γ(T,⊤))) := by
  let D := ProjectiveSpectrum.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)
  let U := h ⁻¹ᵁ D
  have hs := Stacks.ProjectiveSpaceModuli.resT_pullbackCoordSection_of_le
    h i j (W := U) le_rfl
  have ht := congrArg (fun s => e.hom.app U s) hs
  have hn (k : Fin (n+1)) :
      e.hom.app U (resT U (pullbackCoordSection h k)) =
        (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((e.hom.app ⊤ (pullbackCoordSection h k) : Γ(T,⊤))) :=
    PresheafOfModules.naturality_apply e.hom.val
      (homOfLE (le_top : U ≤ ⊤)).op (pullbackCoordSection h k)
  rw [Scheme.Modules.Hom.app_smul,hn j,hn i] at ht
  rw [← chartFracSection_eq_away] at ht
  simp only [U,D,AlgebraicGeometry.Proj.basicOpen,Scheme.Hom.appLE_eq_app,smul_eq_mul] at ht
  exact ht.symm

end NativeProjective

variable (K : Type u) [Field K] [CharZero K]
variable {T : Scheme.{u}} (f : T ⟶ space K)

/-- The original integral O(1)-determinant isomorphism, genuinely pulled
through the composite morphism. -/
def positiveLineIso :
    (Scheme.Modules.pullback (f ≫ LagrangianPlucker.integralPrimitivePlucker K)).obj
        (twistingSheafAtUniverse.{u} 13) ≅
      (Scheme.Modules.pullback f).obj (determinantLine K) :=
  ((Scheme.Modules.pullbackComp f (LagrangianPlucker.integralPrimitivePlucker K)).app
    (twistingSheafAtUniverse.{u} 13)).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (integralDeterminantLineIso K)

theorem positiveLineIso_coordinate (j : Fin 14) :
    (positiveLineIso K f).hom.app ⊤
      (pullbackCoordSection (f ≫ LagrangianPlucker.integralPrimitivePlucker K) j) =
        pullbackGlobalSections f (determinantLine K) (primitiveSections K j) := by
  change (((Scheme.Modules.pullback f).mapIso (integralDeterminantLineIso K)).hom).app ⊤
    ((((Scheme.Modules.pullbackComp f (LagrangianPlucker.integralPrimitivePlucker K)).app
      (twistingSheafAtUniverse.{u} 13)).inv).app ⊤
        (pullbackGlobalSections (f ≫ LagrangianPlucker.integralPrimitivePlucker K)
          (twistingSheafAtUniverse.{u} 13) (coordGlobalSection.{u} 13 j))) = _
  simp only [CategoryTheory.Functor.mapIso_hom,Iso.app_inv]
  rw [LineFramePullback.pullbackComp_inv_apply,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]
  exact congrArg (fun s => pullbackGlobalSections f (determinantLine K) s)
    (integralDeterminantLineIso_coordinate K j)

def framedCoordinate
    (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅
      SheafOfModules.unit T.ringCatSheaf) (j : Fin 14) : Γ(T,⊤) :=
  e.hom.app ⊤ (pullbackGlobalSections f (determinantLine K) (primitiveSections K j))

/-- The literal product identity for the ORIGINAL fourteen determinant
sections, valid in every actual pulled-back determinant frame. -/
theorem primitive_ratio_product
    (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅
      SheafOfModules.unit T.ringCatSheaf) (i j : Fin 14) :
    let h := f ≫ LagrangianPlucker.integralPrimitivePlucker K
    let D := ProjectiveSpectrum.basicOpen (coordGrading.{u} 13) (MvPolynomial.X i)
    let U := h ⁻¹ᵁ D
    (h.app D).hom (chartFracSection (ULift.{u} ℤ) 13 i j) *
        (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (framedCoordinate K f e i) =
      (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (framedCoordinate K f e j) := by
  have h := framed_ratio_product (f ≫ LagrangianPlucker.integralPrimitivePlucker K)
    (positiveLineIso K f ≪≫ e) i j
  simpa only [Iso.trans_hom,Scheme.Modules.Hom.comp_app,CategoryTheory.comp_apply,
    positiveLineIso_coordinate,framedCoordinate] using h

end M9Native.LagrangianProjectiveRatio

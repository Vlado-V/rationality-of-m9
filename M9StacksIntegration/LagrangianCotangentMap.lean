module

public import M9StacksIntegration.LagrangianLocalPairing

/-! The intrinsic actual sheaf map from the symmetric square of the
dual isotropic quotient to the native relative cotangent sheaf. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators TensorProduct

universe u

namespace M9Native.LagrangianCotangentMap

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianLocalPairing LagrangianSymmetricLiftNaturality
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X S : Scheme.{u}} {Q : X.Modules}

/-- The actual sectionwise symmetric-square lift of the intrinsic pairing. -/
def localSquareMap (p : X ⟶ S) (q : freeOn X 6 ⟶ Q) (hq : AnnihilatesSigma X q)
    (U : X.Opens) :
    SymPow.symmetricPower 2 Γ(X,U) Γ(dualSheaf Q,U) →ₗ[Γ(X,U)]
      Γ(Scheme.Hom.relativeDifferentials p,U) :=
  SymPow.sqLift (localPairing p q hq U) (localPairing_symmetric p q hq U)

@[simp] theorem localSquareMap_product (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (U : X.Opens) (α β : Γ(dualSheaf Q,U)) :
    localSquareMap p q hq U (SymPow.sqMul LinearMap.id (α ⊗ₜ[Γ(X,U)] β))=
      localPairing p q hq U α β :=
  SymPow.sqLift_sqMul_tmul _ _ _ _

theorem localSquareMap_map (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) {U V : X.Opens} (h : V≤U)
    (x : SymPow.symmetricPower 2 Γ(X,U) Γ(dualSheaf Q,U)) :
    (Scheme.Hom.relativeDifferentials p).presheaf.map (homOfLE h).op
      (localSquareMap p q hq U x)=
      localSquareMap p q hq V
        (SymPow.symMapₛₗ 2 (X.presheaf.map (homOfLE h).op).hom
          ((dualSheaf Q).val.restrictₛₗ (homOfLE h).op) x) :=
  sqLift_naturality (R := Γ(X,U)) (S := Γ(X,V))
    (X.presheaf.map (homOfLE h).op).hom
    ((dualSheaf Q).val.restrictₛₗ (homOfLE h).op)
    ((Scheme.Hom.relativeDifferentials p).val.restrictₛₗ (homOfLE h).op)
    _ _ _ _ (localPairing_map p q hq h) x

/-- The sectionwise formula as a genuine morphism of presheaves of
modules. Its compatibility on every open was derived from the original
quotient equation and the actual universal derivation. -/
def presheafMap (p : X ⟶ S) (q : freeOn X 6 ⟶ Q) (hq : AnnihilatesSigma X q) :
    PresheafOfModules.symPowInt (O := X.sheaf.obj) 2 (dualSheaf Q).val ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        (Scheme.Hom.relativeDifferentials p).val where
  app U := ModuleCat.ofHom (localSquareMap p q hq U.unop)
  naturality := by
    intro U V f
    ext x
    exact (localSquareMap_map p q hq (leOfHom f.unop) x).symm

/-- The canonical global cotangent map, obtained by the actual native
symmetric-power sheafification universal property. No isomorphism or
Jacobian identity is part of its definition. -/
def cotangentMap (p : X ⟶ S) (q : freeOn X 6 ⟶ Q) (hq : AnnihilatesSigma X q) :
    symmetricSquare (dualSheaf Q) ⟶ Scheme.Hom.relativeDifferentials p :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (presheafMap p q hq)

theorem cotangentMap_sheafification (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
      (cotangentMap p q hq)=presheafMap p q hq :=
  Equiv.apply_symm_apply _ _

end M9Native.LagrangianCotangentMap

module

public import M9StacksIntegration.LagrangianCotangentPullbackNaturality
public import M9StacksIntegration.LagrangianSymmetricPullbackHomExt

/-! The actual sheaf cotangent map commutes with the original scheme pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.LagrangianCotangentPullbackMap

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianCotangentMap LagrangianCotangentSections LagrangianLocalPairing
open LagrangianCotangentPullbackNaturality LagrangianIsotropicRestriction
open LagrangianSymmetricPullback LagrangianSymmetricPullbackProduct
open LagrangianSymmetricPullbackHomExt
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X Y S : Scheme.{u}} {Q : Y.Modules}

/-- The inverse of the genuine symmetric pullback comparison takes the
actual pullback of a local product to the product of its actual units. -/
theorem symmetricPullbackIso_inv_product (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (α β : Γ(F,U)) :
    (symmetricPullbackIso g F 2).inv.val.app (op (g ⁻¹ᵁ U))
      (pullbackUnit g ((Scheme.Modules.symmetricAlgebra Y F).piece 2) U (product F U α β))=
    product ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U)
      (pullbackUnit g F U α) (pullbackUnit g F U β) := by
  let e := symmetricPullbackIso g F 2
  have h := congrArg (fun z => e.inv.val.app (op (g ⁻¹ᵁ U)) z)
    (symmetricPullbackIso_product g F U α β)
  exact h.symm.trans (SheafOfModules.iso_inv_hom_app_apply e (op (g ⁻¹ᵁ U)) _)

/-- The original global cotangent map retains its original unscaled
bilinear formula on literal native local products. -/
theorem cotangentMap_product {T B : Scheme.{u}} {F : T.Modules}
    (p : T ⟶ B) (q : freeOn T 6 ⟶ F) (hq : AnnihilatesSigma T q)
    (U : T.Opens) (α β : Γ(dualSheaf F,U)) :
    (cotangentMap p q hq).val.app (op U) (product (dualSheaf F) U α β)=
      localPairing p q hq U α β :=
  cotangentMap_squareUnit_product p q hq U α β

/-- The right side of naturality is the actual symmetric-dual
base-change morphism followed by the actual intrinsic cotangent map. -/
def pulledCotangentMap (g : X ⟶ Y) (p : Y ⟶ S)
    (q : freeOn Y 6 ⟶ Q) (hq : AnnihilatesSigma Y q) :
    (Scheme.Modules.pullback g).obj (symmetricSquare (dualSheaf Q)) ⟶
      Scheme.Hom.relativeDifferentials (g ≫ p) :=
  (symmetricPullbackIso g (dualSheaf Q) 2).inv ≫
    symmetricMap (Stacks.Chow.pullbackDualMap g Q) 2 ≫
      cotangentMap (g ≫ p) (pulledQuotient g q) (pulledQuotient_annihilates g q hq)

/-- This computation is on the original local products and the
original pullback unit, with every comparison normalization derived. -/
theorem pulledCotangentMap_product (g : X ⟶ Y) (p : Y ⟶ S)
    (q : freeOn Y 6 ⟶ Q) (hq : AnnihilatesSigma Y q)
    (U : Y.Opens) (α β : Γ(dualSheaf Q,U)) :
    (pulledCotangentMap g p q hq).val.app (op (g ⁻¹ᵁ U))
      (pullbackUnit g (symmetricSquare (dualSheaf Q)) U (product (dualSheaf Q) U α β))=
    localPairing (g ≫ p) (pulledQuotient g q) (pulledQuotient_annihilates g q hq)
      (g ⁻¹ᵁ U) (dualSections g Q U α) (dualSections g Q U β) := by
  have h₀ := symmetricPullbackIso_inv_product g (dualSheaf Q) U α β
  have h₁ := symmetricMap_product (Stacks.Chow.pullbackDualMap g Q) (g ⁻¹ᵁ U)
    (pullbackUnit g (dualSheaf Q) U α) (pullbackUnit g (dualSheaf Q) U β)
  have h₂ := cotangentMap_product (g ≫ p) (pulledQuotient g q)
    (pulledQuotient_annihilates g q hq) (g ⁻¹ᵁ U)
      (dualSections g Q U α) (dualSections g Q U β)
  exact (congrArg (fun z =>
      (cotangentMap (g ≫ p) (pulledQuotient g q)
        (pulledQuotient_annihilates g q hq)).val.app (op (g ⁻¹ᵁ U))
          ((symmetricMap (Stacks.Chow.pullbackDualMap g Q) 2).val.app (op (g ⁻¹ᵁ U)) z)) h₀).trans
    ((congrArg (fun z =>
      (cotangentMap (g ≫ p) (pulledQuotient g q)
        (pulledQuotient_annihilates g q hq)).val.app (op (g ⁻¹ᵁ U)) z) h₁).trans h₂)

/-- Naturality of the actual global sheaf cotangent map under every
actual scheme pullback. Neither a cotangent isomorphism nor a Jacobian
or compatibility assertion is a premise. -/
theorem cotangentMap_pullback (g : X ⟶ Y) (p : Y ⟶ S)
    (q : freeOn Y 6 ⟶ Q) (hq : AnnihilatesSigma Y q) :
    (Scheme.Modules.pullback g).map (cotangentMap p q hq) ≫ differentialMap g p=
      pulledCotangentMap g p q hq := by
  apply hom_ext_products g (dualSheaf Q)
  intro U α β
  have hn := Stacks.Chow.pullback_map_unit_app g (cotangentMap p q hq) U
    (product (dualSheaf Q) U α β)
  have hl : ((Scheme.Modules.pullback g).map (cotangentMap p q hq)).val.app
      (op (g ⁻¹ᵁ U))
      (pullbackUnit g (symmetricSquare (dualSheaf Q)) U (product (dualSheaf Q) U α β))=
    pullbackUnit g (Scheme.Hom.relativeDifferentials p) U
      ((cotangentMap p q hq).val.app (op U) (product (dualSheaf Q) U α β)) := hn
  have hprod := cotangentMap_product p q hq U α β
  exact (congrArg (fun z => (differentialMap g p).val.app (op (g ⁻¹ᵁ U)) z) hl).trans
    ((congrArg (fun z => (differentialMap g p).val.app (op (g ⁻¹ᵁ U))
      (pullbackUnit g (Scheme.Hom.relativeDifferentials p) U z)) hprod).trans
      ((localPairing_pullback g p q hq U α β).trans
        (pulledCotangentMap_product g p q hq U α β).symm))

end M9Native.LagrangianCotangentPullbackMap

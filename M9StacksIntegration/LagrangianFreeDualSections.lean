module

public import M9StacksIntegration.LagrangianLocalIsotropy
public import M9StacksIntegration.LagrangianSectionGeneration

/-! Actual dual sections and literal free quotient coefficients. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianFreeDualSections

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianIsotropicDual LagrangianLocalIsotropy LagrangianPluckerQuotient
open LagrangianSectionGeneration
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- The actual dual's global sections are precisely the actual sheaf
functionals, with both inverses computed on every open. -/
def topFunctionalEquiv (Q : X.Modules) :
    Γ(dualSheaf Q,⊤) ≃ (Q ⟶ SheafOfModules.unit X.ringCatSheaf) where
  toFun := topFunctional Q
  invFun := functionalSection Q
  left_inv α := by
    apply dualPairing_ext
    intro W s
    change (α.app (op (Over.mk (homOfLE (show W.left≤⊤ from le_top))))).hom s=
      (α.app (op W)).hom s
    cases W
    congr 3
  right_inv f := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    rfl

/-- Genuine maps from a finite free sheaf to the unit are determined by
their actual standard global basis values. -/
def freeFunctionalEquiv (X : Scheme.{u}) (r : ℕ) :
    (freeOn X r ⟶ SheafOfModules.unit X.ringCatSheaf) ≃ (Fin r → Γ(X,⊤)) where
  toFun f i := f.app ⊤ (freeBasisSection X r i)
  invFun s := sectionMap X (SheafOfModules.unit X.ringCatSheaf) s
  left_inv f := by
    apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin r)))
    intro i
    apply unitHom_ext_top_one
    change (sectionMap X (SheafOfModules.unit X.ringCatSheaf)
      (fun j => f.app ⊤ (freeBasisSection X r j))).app ⊤ (freeBasisSection X r i.down)=_
    rw [sectionMap_top_basis]
    rfl
  right_inv s := by
    funext i
    exact sectionMap_top_basis X (SheafOfModules.unit X.ringCatSheaf) s i

def freeDualCoefficientMap (X : Scheme.{u}) (r : ℕ) :
    Γ(dualSheaf (freeOn X r),⊤) →ₗ[Γ(X,⊤)] (Fin r → Γ(X,⊤)) :=
  LinearMap.pi (fun i =>
    { toFun α := evalAt (freeOn X r) α (freeBasisSection X r i)
      map_add' α β := evalAt_add _ α β _
      map_smul' c α := by simpa only [RingHom.id_apply] using evalAt_smul _ c α _ })

/-- The exact genuine dual coordinates of a finite free sheaf. -/
def freeDualCoordinates (X : Scheme.{u}) (r : ℕ) :
    Γ(dualSheaf (freeOn X r),⊤) ≃ₗ[Γ(X,⊤)] (Fin r → Γ(X,⊤)) :=
  LinearEquiv.ofBijective (freeDualCoefficientMap X r) (by
    have h : (freeDualCoefficientMap X r : _ → _) =
        ((topFunctionalEquiv (freeOn X r)).trans (freeFunctionalEquiv X r) : _ → _) := by
      funext α
      funext i
      exact (topFunctional_top (freeOn X r) α (freeBasisSection X r i)).symm
    rw [h]
    exact Equiv.bijective _)

@[simp] theorem freeDualCoordinates_apply (X : Scheme.{u}) (r : ℕ)
    (α : Γ(dualSheaf (freeOn X r),⊤)) (i : Fin r) :
    freeDualCoordinates X r α i=evalAt (freeOn X r) α (freeBasisSection X r i) := rfl

/-- Evaluation of an actual quotient column is the literal matrix
contraction against the original functional's actual free coordinates. -/
theorem coefficientMap_free (q : freeOn X 6 ⟶ freeOn X 3)
    (α : Γ(dualSheaf (freeOn X 3),⊤)) (j : Fin 6) :
    coefficientMap q ⊤ α j=
      ∑ i : Fin 3,Stacks.FreeSheafMatrix.toMatrix q i j * freeDualCoordinates X 3 α i := by
  change evalAt (freeOn X 3) α (quotientVector q ⊤ j)=_
  have hcol := freeSection_eq_sum X 3 (q.app ⊤ (freeVector X j))
  have hc (i : Fin 3) : freeSectionCoordinates X 3 (q.app ⊤ (freeVector X j)) i=
      Stacks.FreeSheafMatrix.toMatrix q i j := freeCoordinates_map_basis q i j
  simp only [hc] at hcol
  have htop : quotientVector q ⊤ j=q.app ⊤ (freeVector X j) := by
    simp [quotientVector]
  rw [htop,hcol]
  change (α.app (op (Over.mk (𝟙 (⊤ : X.Opens))))).hom
    (∑ i : Fin 3,Stacks.FreeSheafMatrix.toMatrix q i j • freeBasisSection X 3 i)=_
  simp only [map_sum,map_smul,freeDualCoordinates_apply,smul_eq_mul]
  rfl

end M9Native.LagrangianFreeDualSections

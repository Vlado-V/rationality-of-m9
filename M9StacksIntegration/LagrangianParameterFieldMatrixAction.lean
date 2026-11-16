module

public import M9StacksIntegration.LagrangianParameterLinearAction
public import M9StacksIntegration.GrassmannianFieldKernels

/-! The genuine native GL14 parameter action on original-field quotient
matrices. Positive precomposition is literal right multiplication M*U.
Surjectivity and the represented quotient class are derived, and equality
of the actual row spans detects equality of the actual field points. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.LagrangianParameterFieldMatrixAction

open LagrangianParameterLinearAction

variable (K : Type u) [Field K]

theorem scalarMap_identity : scalarMap K (𝟙 (Spec (.of K))) =
    (Scheme.ΓSpecIso (.of K)).inv.hom := by
  ext c
  rfl

/-- The actual inverse of U supplies a right inverse of the product. -/
theorem acted_surjective (U : Matrix.GeneralLinearGroup (Fin 14) K)
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec) :
    Function.Surjective (M * U.val).mulVec := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨(U⁻¹).val * SplitMatrixGrassmannian.fieldRightInverse 9 14 K M hM, ?_⟩
  calc
    M * U.val * ((U⁻¹).val * SplitMatrixGrassmannian.fieldRightInverse 9 14 K M hM) =
        M * (U.val * (U⁻¹).val) * SplitMatrixGrassmannian.fieldRightInverse 9 14 K M hM := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Units.mul_inv, Matrix.mul_one]
      exact SplitMatrixGrassmannian.fieldRightInverse_spec 9 14 K M hM

/-- The original split quotient transforms by the SAME native action,
with no assumed quotient-class or action-identification equality. -/
theorem transform_fieldPresentation (U : Matrix.GeneralLinearGroup (Fin 14) K)
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec) :
    transformPoints K (𝟙 (Spec (.of K))) U
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K M hM⟧ =
        ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K (M * U.val)
          (acted_surjective K U M hM)⟧ := by
  change (⟦transform K (𝟙 (Spec (.of K))) U
    (SplitMatrixGrassmannian.fieldPresentation 9 14 K M hM)⟧ :
      AlgebraicGeometry.Grassmannian.Points (Spec (.of K)) 9 14) = _
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _, ?_⟩
  dsimp only [transform]
  simp only [Iso.refl_hom, Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, constantFreeIso_matrix,
    SplitMatrixGrassmannian.fieldPresentation_matrix,
    SplitMatrixGrassmannian.fieldPresentation_matrix]
  change M.map (Scheme.ΓSpecIso (.of K)).inv.hom *
      U.val.map (scalarMap K (𝟙 (Spec (.of K)))) =
    (M * U.val).map (Scheme.ΓSpecIso (.of K)).inv.hom
  rw [scalarMap_identity K, Matrix.map_mul]

theorem fieldPoint_class (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) :
    pointClass K (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K M hM⟧ :=
  SplitMatrixGrassmannian.fieldPoint_class 9 14 K M hM

theorem fieldPoint_action_class (U : Matrix.GeneralLinearGroup (Fin 14) K)
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec) :
    pointClass K (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM ≫ action K U) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 9 14 K (M * U.val)
        (acted_surjective K U M hM)⟧ := by
  rw [pointClass_action K]
  change transformPoints K
    (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM ≫
      GrassmannianCharts.projection K 9 14) U _ = _
  rw [SplitMatrixGrassmannian.fieldPoint_projection, fieldPoint_class K,
    transform_fieldPresentation K]

/-- Equality of actual scheme morphisms, not only equality of matrices
or geometric point sets. The product-surjectivity proof is derived. -/
theorem fieldPoint_action (U : Matrix.GeneralLinearGroup (Fin 14) K)
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec) :
    SplitMatrixGrassmannian.fieldPoint 9 14 K M hM ≫ action K U =
      SplitMatrixGrassmannian.fieldPoint 9 14 K (M * U.val)
        (acted_surjective K U M hM) := by
  apply LagrangianParameterLinearAction.hom_ext K
  · change (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM ≫ action K U) ≫
        GrassmannianCharts.projection K 9 14 = _
    rw [Category.assoc, action_projection]
    exact (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM).trans
      (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K (M * U.val)
        (acted_surjective K U M hM)).symm
  · rw [fieldPoint_action_class K, fieldPoint_class K]

/-- Literal span of the original row functions. -/
def rowSpan {m n : ℕ} (M : Matrix (Fin m) (Fin n) K) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range M.row)

theorem kernel_le_of_rowSpan_le {m n : ℕ} (M N : Matrix (Fin m) (Fin n) K)
    (h : rowSpan K M ≤ rowSpan K N) :
    LinearMap.ker N.mulVecLin ≤ LinearMap.ker M.mulVecLin := by
  intro v hv
  let ev : (Fin n → K) →ₗ[K] K := (dotProductBilin K K).flip v
  have hN : rowSpan K N ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change N.row i ⬝ᵥ v = 0
    exact congrFun hv i
  have hM := h.trans hN
  change M.mulVec v = 0
  funext i
  exact hM (Submodule.subset_span ⟨i, rfl⟩)

theorem kernel_eq_of_rowSpan_eq {m n : ℕ} (M N : Matrix (Fin m) (Fin n) K)
    (h : rowSpan K M = rowSpan K N) :
    LinearMap.ker M.mulVecLin = LinearMap.ker N.mulVecLin :=
  le_antisymm (kernel_le_of_rowSpan_le K N M h.ge)
    (kernel_le_of_rowSpan_le K M N h.le)

theorem fieldPoint_eq_of_rowSpan_eq (M N : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (h : rowSpan K M = rowSpan K N) :
    SplitMatrixGrassmannian.fieldPoint 9 14 K M hM =
      SplitMatrixGrassmannian.fieldPoint 9 14 K N hN :=
  (GrassmannianFieldKernels.fieldPoint_eq_iff_kernel_eq (k := 9) (n := 14) (K := K)
    M N hM hN).mpr (kernel_eq_of_rowSpan_eq K M N h)

/-- A literal row-span computation on M*U proves the original native
parameter-action equality, without supplying that equality as a premise. -/
theorem fieldPoint_action_eq_of_rowSpan_eq (U : Matrix.GeneralLinearGroup (Fin 14) K)
    (M N : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (h : rowSpan K (M * U.val) = rowSpan K N) :
    SplitMatrixGrassmannian.fieldPoint 9 14 K M hM ≫ action K U =
      SplitMatrixGrassmannian.fieldPoint 9 14 K N hN := by
  rw [fieldPoint_action K]
  exact fieldPoint_eq_of_rowSpan_eq K _ N (acted_surjective K U M hM) hN h

end M9Native.LagrangianParameterFieldMatrixAction

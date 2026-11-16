module

public import M9StacksIntegration.LagrangianModelRestriction
public import M9StacksIntegration.LagrangianGeometricGenericSections
public import M9StacksIntegration.LagrangianGoodOpenFibreSmoothness

/-! Original primitive restriction on every actual matrix parameter of
the canonical good open.  Integrality and smoothness are derived from
the proved original family, so no prefix or curve-geometry premise is
required for the five-row kernel and nine-dimensional image. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.LagrangianGoodOpenRestriction

open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianMatrixPointRows LagrangianGeometricFibre LagrangianOrderedFibre

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
variable (hg : matrixPoint K M hM (IsLocalRing.closedPoint K) ∈ goodOpen K)

section AtMatrix
include hg

theorem fibre_integral : IsIntegral (geometricFibre K M hM) := by
  have hp : ∀ t : Spec (.of K), matrixPoint K M hM t ∈ goodOpen K := by
    intro t
    simpa only [Subsingleton.elim t (IsLocalRing.closedPoint K)] using hg
  let : IsIntegral (pullback (familyProjection K ∣_ goodOpen K)
      (OpenRestrictionPointFiber.lift (goodOpen K) (matrixPoint K M hM) hp)) := by
    exact LagrangianGeometricGenericSections.baseChange_integral K K
      (OpenRestrictionPointFiber.lift (goodOpen K) (matrixPoint K M hM) hp)
  exact IsIntegral.of_isIso
    (OpenRestrictionPointFiber.fiberIso (familyProjection K) (goodOpen K)
      (matrixPoint K M hM) hp).hom

omit [IsAlgClosed K] in
theorem fibre_smooth : SmoothOfRelativeDimension 1
    (pullback.snd (familyProjection K) (matrixPoint K M hM)) :=
  LagrangianGoodOpenFibreSmoothness.fieldPoint_fibre_smoothOfRelativeDimension K K
    (matrixPoint K M hM) hg

theorem model_integral : IsIntegral (model K M hM) := by
  let : IsIntegral (geometricFibre K M hM) := fibre_integral K M hM hg
  exact IsIntegral.of_isIso (modelIsoFibre K M hM).inv

omit [IsAlgClosed K] in
theorem model_smooth : SmoothOfRelativeDimension 1 (modelProjection K M hM) := by
  let : SmoothOfRelativeDimension 1
      (pullback.snd (familyProjection K) (matrixPoint K M hM)) := fibre_smooth K M hM hg
  have h : SmoothOfRelativeDimension (0 + 1)
      ((modelIsoFibre K M hM).hom ≫
        pullback.snd (familyProjection K) (matrixPoint K M hM)) := inferInstance
  have he : (modelIsoFibre K M hM).hom ≫
      pullback.snd (familyProjection K) (matrixPoint K M hM) = modelProjection K M hM := by
    rw [← geometricFibre_over,← Category.assoc,modelIsoFibre_hom_toLG]
  rw [he] at h
  exact h

theorem model_primitiveRestriction_kernel :
    LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (modelProjection K M hM) (modelInclusion K M hM)) =
        Submodule.span K (Set.range M) := by
  let : IsIntegral (model K M hM) := model_integral K M hM hg
  let : SmoothOfRelativeDimension 1 (modelProjection K M hM) := model_smooth K M hM hg
  exact LagrangianModelRestriction.primitiveRestriction_kernel K M hM

theorem model_primitiveRestriction_range_finrank :
    finrank K (LinearMap.range (LagrangianPrimitiveRestriction.primitiveRestriction K
      (modelProjection K M hM) (modelInclusion K M hM))) = 9 := by
  let : IsIntegral (model K M hM) := model_integral K M hM hg
  let : SmoothOfRelativeDimension 1 (modelProjection K M hM) := model_smooth K M hM hg
  exact LagrangianModelRestriction.primitiveRestriction_range_finrank K M hM

/-- The original incidence fibre has the same computed kernel,
without a supplied curve-model comparison. -/
theorem fibre_primitiveRestriction_kernel :
    LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (pullback.snd (familyProjection K) (matrixPoint K M hM)) (geometricFibreToLG K M hM)) =
        Submodule.span K (Set.range M) := by
  have he := LagrangianRestrictionIso.primitiveRestriction_kernel_iso K
    (modelProjection K M hM) (pullback.snd (familyProjection K) (matrixPoint K M hM))
    (modelInclusion K M hM) (geometricFibreToLG K M hM) rfl (geometricFibre_over K M hM)
    (modelIsoFibre K M hM) (modelIsoFibre_hom_toLG K M hM)
  rw [← he]
  exact model_primitiveRestriction_kernel K M hM hg

theorem fibre_primitiveRestriction_range_finrank :
    finrank K (LinearMap.range (LagrangianPrimitiveRestriction.primitiveRestriction K
      (pullback.snd (familyProjection K) (matrixPoint K M hM)) (geometricFibreToLG K M hM))) = 9 := by
  have hd := (LagrangianPrimitiveRestriction.primitiveRestriction K
    (pullback.snd (familyProjection K) (matrixPoint K M hM))
      (geometricFibreToLG K M hM)).finrank_range_add_finrank_ker
  have hk : finrank K (LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (pullback.snd (familyProjection K) (matrixPoint K M hM))
        (geometricFibreToLG K M hM))) = 5 := by
    rw [fibre_primitiveRestriction_kernel K M hM hg]
    have hr := (Matrix.mulVec_surjective_iff_rank_eq_card (M := M)).mp hM
    rw [Matrix.rank_eq_finrank_span_row] at hr
    exact hr
  have h14 : finrank K (Fin 14 → K) = 14 := by simp
  rw [hk,h14] at hd
  omega

end AtMatrix

/-- Every actual original rational parameter in the good open has
the computed five-row kernel and nine-dimensional image. Its matrix
and its identification with the original parameter are derived. -/
theorem every_parameter_restriction (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _)
    (hg : p (IsLocalRing.closedPoint K) ∈ goodOpen K) :
    ∃ (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec),
      p = matrixPoint K M hM ∧
      LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
        (pullback.snd (familyProjection K) p)
        (pullback.fst (familyProjection K) p ≫ familyToLG K)) =
          Submodule.span K (Set.range M) ∧
      finrank K (LinearMap.range (LagrangianPrimitiveRestriction.primitiveRestriction K
        (pullback.snd (familyProjection K) p)
        (pullback.fst (familyProjection K) p ≫ familyToLG K))) = 9 := by
  obtain ⟨M,hM,rfl⟩ := LagrangianParameterMatrix.exists_matrix K p hp
  exact ⟨M,hM,rfl,fibre_primitiveRestriction_kernel K M hM hg,
    fibre_primitiveRestriction_range_finrank K M hM hg⟩

end M9Native.LagrangianGoodOpenRestriction
end

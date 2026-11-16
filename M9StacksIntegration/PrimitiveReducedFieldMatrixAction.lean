module

public import M9StacksIntegration.PrimitiveRadicalSliceField

@[expose] public section

/-! Native reduced field points under actual extension-field matrices.
This is a field-point quotient computation; it assumes no algebraic-group
scheme or rational-function invariance theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped Classical Matrix

namespace M9Native.PrimitiveReducedFieldMatrixAction

variable (K : Type) [Field K]

abbrev space := GrassmannianCharts.space ℂ 4 12

/-- The original native quotient class is transformed over Spec K by the
actual field matrix, then classified over its unchanged original complex base. -/
def fieldAction (M : Matrix.GeneralLinearGroup (Fin 12) K) (p : Spec (.of K) ⟶ space) :
    Spec (.of K) ⟶ space :=
  GraphGrassmannianLinearAction.classify ℂ (p ≫ GrassmannianCharts.projection ℂ 4 12)
    (GraphGrassmannianLinearAction.transformPoints K (𝟙 (Spec (.of K))) M
      (GraphGrassmannianLinearAction.pointClass ℂ p))

@[reassoc] theorem fieldAction_projection (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (p : Spec (.of K) ⟶ space) :
    fieldAction K M p ≫ GrassmannianCharts.projection ℂ 4 12 =
      p ≫ GrassmannianCharts.projection ℂ 4 12 :=
  GraphGrassmannianLinearAction.classify_projection ℂ _ _

theorem fieldAction_class (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (p : Spec (.of K) ⟶ space) :
    GraphGrassmannianLinearAction.pointClass ℂ (fieldAction K M p) =
      GraphGrassmannianLinearAction.transformPoints K (𝟙 (Spec (.of K))) M
        (GraphGrassmannianLinearAction.pointClass ℂ p) :=
  GraphGrassmannianLinearAction.classify_class ℂ _ _

theorem scalarMap_identity : GraphGrassmannianLinearAction.scalarMap K (𝟙 (Spec (.of K))) =
    (Scheme.ΓSpecIso (.of K)).inv.hom := by
  ext c
  rfl

theorem acted_surjective (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (Q : Matrix (Fin 8) (Fin 12) K) (hQ : Function.Surjective Q.mulVec) :
    Function.Surjective (Q * M.val).mulVec := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨(M⁻¹).val * SplitMatrixGrassmannian.fieldRightInverse 4 12 K Q hQ,?_⟩
  calc
    Q * M.val * ((M⁻¹).val * SplitMatrixGrassmannian.fieldRightInverse 4 12 K Q hQ) =
      Q * (M.val * (M⁻¹).val) * SplitMatrixGrassmannian.fieldRightInverse 4 12 K Q hQ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [Units.mul_inv,Matrix.mul_one]
      exact SplitMatrixGrassmannian.fieldRightInverse_spec 4 12 K Q hQ

theorem transform_fieldPresentation (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (Q : Matrix (Fin 8) (Fin 12) K) (hQ : Function.Surjective Q.mulVec) :
    GraphGrassmannianLinearAction.transformPoints K (𝟙 (Spec (.of K))) M
      ⟦SplitMatrixGrassmannian.fieldPresentation 4 12 K Q hQ⟧ =
      ⟦SplitMatrixGrassmannian.fieldPresentation 4 12 K (Q * M.val) (acted_surjective K M Q hQ)⟧ := by
  change (⟦GraphGrassmannianLinearAction.transform K (𝟙 (Spec (.of K))) M
    (SplitMatrixGrassmannian.fieldPresentation 4 12 K Q hQ)⟧ :
      AlgebraicGeometry.Grassmannian.Points (Spec (.of K)) 4 12) = _
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _,?_⟩
  dsimp only [GraphGrassmannianLinearAction.transform]
  simp only [Iso.refl_hom,Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,GraphGrassmannianLinearAction.constantFreeIso_matrix,
    SplitMatrixGrassmannian.fieldPresentation_matrix,SplitMatrixGrassmannian.fieldPresentation_matrix]
  change Q.map (Scheme.ΓSpecIso (.of K)).inv.hom *
      M.val.map (GraphGrassmannianLinearAction.scalarMap K (𝟙 (Spec (.of K)))) =
    (Q * M.val).map (Scheme.ΓSpecIso (.of K)).inv.hom
  rw [scalarMap_identity,Matrix.map_mul]

theorem fieldAction_fieldPresentation (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (p : Spec (.of K) ⟶ space) (Q : Matrix (Fin 8) (Fin 12) K)
    (hQ : Function.Surjective Q.mulVec)
    (hp : GraphGrassmannianLinearAction.pointClass ℂ p =
      ⟦SplitMatrixGrassmannian.fieldPresentation 4 12 K Q hQ⟧) :
    GraphGrassmannianLinearAction.pointClass ℂ (fieldAction K M p) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 4 12 K (Q * M.val) (acted_surjective K M Q hQ)⟧ := by
  rw [fieldAction_class,hp]
  exact transform_fieldPresentation K M Q hQ

theorem kernel_mul_inverse (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (Q : Matrix (Fin 8) (Fin 12) K) :
    (Matrix.toLin' (Q * (M⁻¹).val)).ker = (Matrix.toLin' Q).ker.map (Matrix.toLin' M.val) := by
  ext v
  constructor
  · intro hv
    change (Q * (M⁻¹).val) *ᵥ v = 0 at hv
    rw [← Matrix.mulVec_mulVec] at hv
    refine ⟨(M⁻¹).val *ᵥ v,hv,?_⟩
    change M.val *ᵥ ((M⁻¹).val *ᵥ v) = v
    rw [Matrix.mulVec_mulVec,Units.mul_inv,Matrix.one_mulVec]
  · rintro ⟨u,hu,rfl⟩
    change (Q * (M⁻¹).val) *ᵥ (M.val *ᵥ u) = 0
    have hc : (M⁻¹).val *ᵥ (M.val *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec,Units.inv_mul,Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec,hc]
    exact hu

variable [Algebra ℂ K]

/-- A literal reduced graph-range relation proves equality of the actual
native field-point transform, with the exact inverse convention. -/
theorem fieldAction_graph_points (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (f g : PrimitiveRhoFiberNondegenerate.nondegenerateRing →ₐ[ℂ] K)
    (h : (Matrix.toLin' (PrimitiveRhoFiberNondegenerate.localizedGraph.map g)).range =
      ((Matrix.toLin' (PrimitiveRhoFiberNondegenerate.localizedGraph.map f)).range).map
        (Matrix.toLin' M.val)) :
    fieldAction K M⁻¹ (PrimitiveRhoGraphNativePoints.point K f) =
      PrimitiveRhoGraphNativePoints.point K g := by
  have hb : fieldAction K M⁻¹ (PrimitiveRhoGraphNativePoints.point K f) ≫
        GrassmannianCharts.projection ℂ 4 12 =
      PrimitiveRhoGraphNativePoints.point K g ≫ GrassmannianCharts.projection ℂ 4 12 := by
    rw [fieldAction_projection,PrimitiveRhoGraphNativePoints.point_projection,
      PrimitiveRhoGraphNativePoints.point_projection]
  apply (GrassmannianFieldKernels.points_eq_iff_kernel_eq (K := K) (k := 4) (n := 12)
    (fieldAction K M⁻¹ (PrimitiveRhoGraphNativePoints.point K f)) (PrimitiveRhoGraphNativePoints.point K g)
    (PrimitiveRhoGraphNativePoints.quotient K f * (M⁻¹).val) (PrimitiveRhoGraphNativePoints.quotient K g)
    (acted_surjective K M⁻¹ _ (PrimitiveRhoGraphNativePoints.quotient_surjective K f))
    (PrimitiveRhoGraphNativePoints.quotient_surjective K g)
    (fieldAction_fieldPresentation K M⁻¹ _ _ (PrimitiveRhoGraphNativePoints.quotient_surjective K f)
      (PrimitiveRhoGraphNativePoints.point_class K f))
    (PrimitiveRhoGraphNativePoints.point_class K g) hb).mpr
  change (Matrix.toLin' (PrimitiveRhoGraphNativePoints.quotient K f * (M⁻¹).val)).ker =
    (Matrix.toLin' (PrimitiveRhoGraphNativePoints.quotient K g)).ker
  rw [kernel_mul_inverse,PrimitiveRhoGraphNativePoints.quotient_kernel,
    PrimitiveRhoGraphNativePoints.quotient_kernel]
  exact h.symm

local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K

/-- The actual native orbit-family kernel pair is related by the actual
reduced matrix action on native Gr4 field points, with no invariance premise. -/
theorem field_kernel_pair_relation
    (s t : PrimitiveRadicalOrbitFamily.source.functionField →ₐ[ℂ] K)
    (h : s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding =
      t.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding) :
    ∃ w : ReducedGraphAction.Stabilizer K,
      fieldAction K (ReducedGraphAction.matrixRepresentation K w)⁻¹
        (NativeGenericPullbackEvaluation.point (s.comp PrimitiveRadicalSliceField.sliceEmbedding).toRingHom) =
      NativeGenericPullbackEvaluation.point (t.comp PrimitiveRadicalSliceField.sliceEmbedding).toRingHom := by
  obtain ⟨w,hw⟩ := PrimitiveRadicalOrbitGenericPoints.exists_graph_relation_of_target_embeddings_eq K s t h
  refine ⟨w,?_⟩
  rw [← PrimitiveRadicalSliceField.slicePoint_sourcePoint,← PrimitiveRadicalSliceField.slicePoint_sourcePoint]
  exact fieldAction_graph_points K (ReducedGraphAction.matrixRepresentation K w) _ _ hw

end M9Native.PrimitiveReducedFieldMatrixAction

module

public import M9StacksIntegration.PrimitiveReducedFieldMatrixAction
public import M9StacksIntegration.PrimitiveConstantOriginalExtension

@[expose] public section

/-! Composition and literal constant-coefficient compatibility of the actual
native reduced matrix field-point operation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical Matrix

namespace M9Native.PrimitiveReducedFieldMatrixComposition
open PrimitiveReducedFieldMatrixAction

variable (K : Type) [Field K]

theorem fieldAction_one (p : Spec (.of K) ⟶ space) : fieldAction K 1 p = p := by
  apply GraphGrassmannianLinearAction.hom_ext ℂ
  · exact fieldAction_projection K 1 p
  · rw [fieldAction_class,GraphGrassmannianLinearAction.transformPoints_one]

/-- The composition order is the actual positive quotient-matrix order. -/
theorem fieldAction_mul (M N : Matrix.GeneralLinearGroup (Fin 12) K)
    (p : Spec (.of K) ⟶ space) :
    fieldAction K N (fieldAction K M p) = fieldAction K (M*N) p := by
  apply GraphGrassmannianLinearAction.hom_ext ℂ
  · rw [fieldAction_projection,fieldAction_projection,fieldAction_projection]
  · rw [fieldAction_class,fieldAction_class,fieldAction_class,
      GraphGrassmannianLinearAction.transformPoints_mul]

variable [Algebra ℂ K]

theorem transformPoints_coefficients (M : Matrix.GeneralLinearGroup (Fin 12) ℂ)
    (x : AlgebraicGeometry.Grassmannian.Points (Spec (.of K)) 4 12) :
    GraphGrassmannianLinearAction.transformPoints ℂ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) M x =
    GraphGrassmannianLinearAction.transformPoints K (𝟙 (Spec (.of K)))
      (Matrix.GeneralLinearGroup.map (algebraMap ℂ K) M) x := by
  have hs : GraphGrassmannianLinearAction.scalarMap ℂ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) =
        (Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap ℂ K) :=
    PrimitiveConstantOriginalExtension.scalarMap_spec_inverse K
  have he : (GraphGrassmannianLinearAction.constantFreeIso ℂ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) M).hom =
    (GraphGrassmannianLinearAction.constantFreeIso K (𝟙 (Spec (.of K)))
      (Matrix.GeneralLinearGroup.map (algebraMap ℂ K) M)).hom := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [GraphGrassmannianLinearAction.constantFreeIso_matrix,
      GraphGrassmannianLinearAction.constantFreeIso_matrix]
    change M.val.map (GraphGrassmannianLinearAction.scalarMap ℂ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) =
        (M.val.map (algebraMap ℂ K)).map
          (GraphGrassmannianLinearAction.scalarMap K (𝟙 (Spec (.of K))))
    rw [hs,scalarMap_identity,Matrix.map_map]
    rfl
  refine Quotient.inductionOn x (fun q => ?_)
  apply Quotient.sound
  refine .rel _ _ ⟨Iso.refl _,?_⟩
  change ((GraphGrassmannianLinearAction.constantFreeIso ℂ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) M).hom ≫ q.map) ≫ 𝟙 _ =
    (GraphGrassmannianLinearAction.constantFreeIso K (𝟙 (Spec (.of K)))
      (Matrix.GeneralLinearGroup.map (algebraMap ℂ K) M)).hom ≫ q.map
  rw [Category.comp_id,he]

/-- The field-point operation on a scalar-extended constant matrix is
literally the frozen original native scheme action. -/
theorem fieldAction_constant (M : Matrix.GeneralLinearGroup (Fin 12) ℂ)
    (p : Spec (.of K) ⟶ space)
    (hp : p ≫ GrassmannianCharts.projection ℂ 4 12 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) :
    fieldAction K (Matrix.GeneralLinearGroup.map (algebraMap ℂ K) M) p =
      p ≫ GraphGrassmannianLinearAction.action ℂ M := by
  apply GraphGrassmannianLinearAction.hom_ext ℂ
  · rw [fieldAction_projection,Category.assoc,GraphGrassmannianLinearAction.action_projection]
  · rw [fieldAction_class,GraphGrassmannianLinearAction.pointClass_action,hp]
    exact (transformPoints_coefficients K M _).symm

theorem fieldAction_constant_genericPoint (M : Matrix.GeneralLinearGroup (Fin 12) ℂ)
    (s : (GrassmannianCharts.space ℂ 4 12).functionField →ₐ[ℂ] K) :
    fieldAction K (Matrix.GeneralLinearGroup.map (algebraMap ℂ K) M)
        (NativeGenericPullbackEvaluation.point s.toRingHom) =
      NativeGenericPullbackEvaluation.point
        (s.comp (GraphGrassmannianLinearAction.fieldAutomorphism ℂ M).toAlgHom).toRingHom := by
  rw [fieldAction_constant K M _
    (NativeGenericFieldPoints.point_projection ℂ (GrassmannianCharts.projection ℂ 4 12) rfl s)]
  have h := NativeGenericPointNaturality.point_comp_dominant
    (GraphGrassmannianLinearAction.action ℂ M) s.toRingHom
  rw [← GraphGrassmannianLinearAction.fieldAutomorphism_eq_map] at h
  exact h

end M9Native.PrimitiveReducedFieldMatrixComposition

module

public import M9StacksIntegration.GraphFieldEvaluation

/-! Native graph action and its literal field-matrix criterion.  The
criterion is a proved sufficient condition on the original quotient
kernels, not an assumption identifying any invariant field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.GraphFieldAction

open M9.GraphBundleDescent GraphGrassmannianChart GraphFieldEvaluation
open AlgebraicGeometry.Grassmannian LagrangianMatrixChart

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

abbrev BaseSpecMap : fieldSpec L ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

abbrev constantUnit (g : GraphGrassmannianLinearAction.GL12 K) :
    Matrix.GeneralLinearGroup (Fin 12) L :=
  Matrix.GeneralLinearGroup.map (algebraMap K L) g

def actionMatrix (e : FF K →ₐ[K] L) (g : GraphGrassmannianLinearAction.GL12 K) :
    Matrix (Fin 8) (Fin 12) L :=
  quotientMatrix K L e * (constantUnit K L g).val

theorem actionMatrix_surjective (e : FF K →ₐ[K] L)
    (g : GraphGrassmannianLinearAction.GL12 K) :
    Function.Surjective (actionMatrix K L e g).mulVec := by
  intro y
  obtain ⟨x, hx⟩ := quotientMatrix_surjective K L e y
  have hc : Function.Surjective (constantUnit K L g).val.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (constantUnit K L g).isUnit
  obtain ⟨z, hz⟩ := hc x
  refine ⟨z, ?_⟩
  rw [actionMatrix, ← Matrix.mulVec_mulVec, hz, hx]

theorem scalarMap_field (c : K) :
    GraphGrassmannianLinearAction.scalarMap K (BaseSpecMap K L) c =
      (Scheme.ΓSpecIso (.of L)).inv (algebraMap K L c) := by
  change ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap K L))).appTop) c = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem transform_fieldPresentation (e : FF K →ₐ[K] L)
    (g : GraphGrassmannianLinearAction.GL12 K) :
    (GraphGrassmannianLinearAction.transform K (BaseSpecMap K L) g
      (SplitMatrixGrassmannian.fieldPresentation 4 12 L (quotientMatrix K L e)
        (quotientMatrix_surjective K L e))).Isomorphic
      (SplitMatrixGrassmannian.fieldPresentation 4 12 L (actionMatrix K L e g)
        (actionMatrix_surjective K L e g)) := by
  refine ⟨Iso.refl _, ?_⟩
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  change Stacks.FreeSheafMatrix.toMatrix
      ((GraphGrassmannianLinearAction.constantFreeIso K (BaseSpecMap K L) g).hom ≫
        (SplitMatrixGrassmannian.fieldPresentation 4 12 L (quotientMatrix K L e)
          (quotientMatrix_surjective K L e)).map) = _
  rw [Stacks.FreeSheafMatrix.toMatrix_comp,
    SplitMatrixGrassmannian.fieldPresentation_matrix,
    SplitMatrixGrassmannian.fieldPresentation_matrix,
    GraphGrassmannianLinearAction.constantFreeIso_matrix,
    actionMatrix, Matrix.map_mul]
  congr 1
  apply Matrix.ext
  intro i j
  exact scalarMap_field K L (g.val i j)

theorem point_action_class (e : FF K →ₐ[K] L)
    (g : GraphGrassmannianLinearAction.GL12 K) :
    GraphGrassmannianLinearAction.pointClass K
      (point K L e ≫ GraphGrassmannianLinearAction.action K g) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 4 12 L (actionMatrix K L e g)
        (actionMatrix_surjective K L e g)⟧ := by
  rw [GraphGrassmannianLinearAction.pointClass_action, point_projection,
    point_class_fieldPresentation]
  exact Quotient.sound (.rel _ _ (transform_fieldPresentation K L e g))

def translatedEmbedding (e : FF K →ₐ[K] L) (σ : L ≃ₐ[K] L) : FF K →ₐ[K] L :=
  σ.toAlgHom.comp e

theorem point_translate (e : FF K →ₐ[K] L) (σ : L ≃ₐ[K] L) :
    point K L (translatedEmbedding K L e σ) =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ point K L e := by
  change Spec.map (CommRingCat.ofHom (σ.toAlgHom.comp e).toRingHom) ≫ _ =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _)
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The actual native action is detected by the literal generic quotient
kernels after coefficient translation. -/
theorem point_action_eq_of_kernel_eq (e : FF K →ₐ[K] L)
    (g : GraphGrassmannianLinearAction.GL12 K) (σ : L ≃ₐ[K] L)
    (hker : LinearMap.ker (actionMatrix K L e g).mulVecLin =
      LinearMap.ker (quotientMatrix K L (translatedEmbedding K L e σ)).mulVecLin) :
    point K L e ≫ GraphGrassmannianLinearAction.action K g =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ point K L e := by
  rw [← point_translate]
  apply GraphGrassmannianLinearAction.hom_ext K
  · rw [Category.assoc, GraphGrassmannianLinearAction.action_projection,
      point_projection, point_projection]
  · rw [point_action_class, point_class_fieldPresentation]
    exact (GrassmannianFieldKernels.fieldPresentation_class_eq_iff_kernel_eq
      (k := 4) (n := 12) (K := L) _ _
        (actionMatrix_surjective K L e g)
        (quotientMatrix_surjective K L (translatedEmbedding K L e σ))).mpr hker

instance specAutomorphism_isDominant (σ : L ≃ₐ[K] L) :
    IsDominant (Spec.map (CommRingCat.ofHom σ.toRingHom)) :=
  NativeDominantFunctionField.specMap_isDominant _ σ.injective

theorem fieldAutomorphism_pullback (σ : L ≃ₐ[K] L) (z : (fieldSpec L).functionField) :
    fieldAffineEquiv L (NativeDominantFunctionField.map
      (Spec.map (CommRingCat.ofHom σ.toRingHom)) z) = σ (fieldAffineEquiv L z) := by
  have hh : (fieldAffineEquiv L).toRingHom.comp
      (NativeDominantFunctionField.map (Spec.map (CommRingCat.ofHom σ.toRingHom))) =
        σ.toRingHom.comp (fieldAffineEquiv L).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := L)
    intro a
    change fieldAffineEquiv L (NativeDominantFunctionField.map
      (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (algebraMap L (fieldSpec L).functionField a)) = _
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, fieldAffineEquiv_algebraMap]
    change σ a = σ (fieldAffineEquiv L (algebraMap L (fieldSpec L).functionField a))
    rw [fieldAffineEquiv_algebraMap]
  exact DFunLike.congr_fun hh z

/-- The kernel criterion gives literal equivariance of the original native
generic-stalk field, with no replacement rational field. -/
theorem field_equivariance_of_kernel_eq (e : FF K →ₐ[K] L)
    (g : GraphGrassmannianLinearAction.GL12 K) (σ : L ≃ₐ[K] L)
    (hker : LinearMap.ker (actionMatrix K L e g).mulVecLin =
      LinearMap.ker (quotientMatrix K L (translatedEmbedding K L e σ)).mulVecLin)
    (z : (GrassmannianCharts.space K 4 12).functionField) :
    e (graphFunctionFieldEquiv K (GraphGrassmannianLinearAction.fieldRepresentation K g z)) =
      σ (e (graphFunctionFieldEquiv K z)) := by
  have hp := point_action_eq_of_kernel_eq K L e g σ hker
  have hh := GraphGrassmannianLinearAction.dominantMap_congr hp
  rw [NativeFunctionFieldFunctor.map_comp, NativeFunctionFieldFunctor.map_comp] at hh
  have hz := congrArg (fieldAffineEquiv L) (DFunLike.congr_fun hh z)
  simp only [RingHom.comp_apply] at hz
  change e (graphFunctionFieldEquiv K (GraphGrassmannianLinearAction.fieldAutomorphism K g z)) = _
  rw [← point_pullback K L e (GraphGrassmannianLinearAction.fieldAutomorphism K g z)]
  change fieldAffineEquiv L (NativeDominantFunctionField.map (point K L e)
    ((GraphGrassmannianLinearAction.fieldAutomorphism K g).toRingHom z)) = _
  rw [GraphGrassmannianLinearAction.fieldAutomorphism_eq_map, hz,
    fieldAutomorphism_pullback, point_pullback]

end M9Native.GraphFieldAction

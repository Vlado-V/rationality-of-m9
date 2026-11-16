module

public import M9StacksIntegration.ConicFrameNativeGeometry
public import M9StacksIntegration.ConicFrameExtension
public import M9StacksIntegration.NativeFunctionFieldFunctor

/-! The native generic-stalk embedding is identified, through its genuine
chart restrictions, with the literal fraction-field extension of the
quotient-coordinate homomorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.ConicFrameFieldComparison

open M9Native.ConicFrameProjective M9Native.ConicFrameCoordinates
open M9Native.ConicFrameCoordinateIndex M9Native.ConicFrameSourceAlgebra
open M9Native.ConicFrameExtension M9Native.ConicFrameNativeGeometry

variable (K : Type u) [Field K] [CharZero K]

/-- The genuine source generic stalk, compared with its proved fraction field. -/
def sourceNativeEquiv : (source K).functionField ≃ₐ[K] rationalField K := by
  let e₁ := (FractionRing.algEquiv (sourceRing K) (source K).functionField).symm
  let e₂ := FractionRing.algEquiv (sourceRing K) (rationalField K)
  refine { __ := e₁.toRingEquiv.trans e₂.toRingEquiv, commutes' := fun c => ?_ }
  have hc : algebraMap K (source K).functionField c =
      algebraMap (sourceRing K) (source K).functionField (algebraMap K (sourceRing K) c) :=
    DFunLike.congr_fun (GrassmannianCharts.affine_structureScalarMap K (sourceRing K)) c
  change e₂ (e₁ (algebraMap K (source K).functionField c)) = _
  rw [hc,e₁.commutes,e₂.commutes]
  exact (IsScalarTower.algebraMap_apply K (sourceRing K) (rationalField K) c).symm

omit [CharZero K] in
theorem sourceNativeEquiv_algebraMap (b : sourceRing K) :
    sourceNativeEquiv K (algebraMap (sourceRing K) (source K).functionField b) = toRational K b := by
  change (FractionRing.algEquiv (sourceRing K) (rationalField K))
    ((FractionRing.algEquiv (sourceRing K) (source K).functionField).symm
      (algebraMap (sourceRing K) (source K).functionField b)) = _
  rw [AlgEquiv.commutes,AlgEquiv.commutes]
  rfl

/-- The native Grassmannian field, restricted through this exact quotient chart. -/
def targetNativeEquiv :
    (GrassmannianCharts.space K 4 6).functionField ≃ₐ[K] targetField K := by
  let e₁ := (GrassmannianCharts.openImmersionFunctionFieldIso
    (GrassmannianCharts.chartSpecMap K 4 6 pivotEmbedding)).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv (targetRing K)
    (Spec (.of (targetRing K))).functionField).symm
  refine { __ := e₁.trans e₂.toRingEquiv, commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K
    (GrassmannianCharts.chartSpecMap K 4 6 pivotEmbedding) (GrassmannianCharts.projection K 4 6)
  rw [GrassmannianCharts.chartSpecMap_projection] at h
  change _ = GrassmannianCharts.structureScalarMap K
    (Spec.map (CommRingCat.ofHom (algebraMap K (targetRing K)))) at h
  rw [GrassmannianCharts.affine_structureScalarMap] at h
  have hc : e₁ (algebraMap K (GrassmannianCharts.space K 4 6).functionField c) =
      algebraMap (targetRing K) (Spec (.of (targetRing K))).functionField
        (algebraMap K (targetRing K) c) := DFunLike.congr_fun h c
  change e₂ (e₁ (algebraMap K (GrassmannianCharts.space K 4 6).functionField c)) = _
  rw [hc,e₂.commutes]
  exact (IsScalarTower.algebraMap_apply K (targetRing K) (targetField K) c).symm

/-- The native projective field is compared through the actual open source
of the rational map, rather than declared to equal a rational field. -/
def projectiveNativeEquiv :
    (ConicFrameProjective.space K).functionField ≃ₐ[K] rationalField K :=
  (sourceRestrictionEquiv K).trans (sourceNativeEquiv K)

theorem affine_pullback_eq (z : (Spec (.of (targetRing K))).functionField) :
    sourceNativeEquiv K
      (NativeDominantFunctionField.map (affineCoordinateMap K) z) =
      targetFieldEmbedding K
        ((FractionRing.algEquiv (targetRing K) (Spec (.of (targetRing K))).functionField).symm z) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (coordinateMap K).toRingHom)) :=
    NativeDominantFunctionField.specMap_isDominant _ (coordinateMap_injective K)
  have h : (sourceNativeEquiv K).toRingHom.comp
        (NativeDominantFunctionField.map (affineCoordinateMap K)) =
      (targetFieldEmbedding K).toRingHom.comp
        (FractionRing.algEquiv (targetRing K) (Spec (.of (targetRing K))).functionField).symm.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := targetRing K)
    intro a
    change sourceNativeEquiv K
      (NativeDominantFunctionField.map (Spec.map (CommRingCat.ofHom (coordinateMap K).toRingHom))
        (algebraMap (targetRing K) (Spec (.of (targetRing K))).functionField a)) =
      targetFieldEmbedding K ((FractionRing.algEquiv (targetRing K)
        (Spec (.of (targetRing K))).functionField).symm
          (algebraMap (targetRing K) (Spec (.of (targetRing K))).functionField a))
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap,sourceNativeEquiv_algebraMap,
      AlgEquiv.commutes,targetFieldEmbedding_algebraMap]
    rfl
  exact DFunLike.congr_fun h z

theorem openIso_eq_map {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsOpenImmersion f] [IsDominant f] :
    (GrassmannianCharts.openImmersionFunctionFieldIso f).hom.hom =
      NativeDominantFunctionField.map f := by
  simp only [GrassmannianCharts.openImmersionFunctionFieldIso,NativeDominantFunctionField.map,
    Iso.trans_hom,asIso_hom]

/-- The actual generic-stalk square commutes with the original quotient
coordinate embedding on fraction fields. -/
theorem embedding_comparison (z : (GrassmannianCharts.space K 4 6).functionField) :
    projectiveNativeEquiv K (functionFieldEmbedding K z) =
      targetFieldEmbedding K (targetNativeEquiv K z) := by
  have : IsDominant (GrassmannianCharts.chartSpecMap K 4 6 pivotEmbedding) :=
    ⟨GrassmannianCharts.chartSpecMap_dense K 4 6 pivotEmbedding⟩
  change sourceNativeEquiv K
      (sourceRestrictionEquiv K ((sourceRestrictionEquiv K).symm
        (NativeDominantFunctionField.map (ConicFrameNativeGeometry.conicMap K) z))) = _
  rw [AlgEquiv.apply_symm_apply]
  change sourceNativeEquiv K (NativeDominantFunctionField.map
    (affineCoordinateMap K ≫ GrassmannianCharts.chartSpecMap K 4 6 pivotEmbedding) z) = _
  rw [NativeFunctionFieldFunctor.map_comp]
  change sourceNativeEquiv K (NativeDominantFunctionField.map (affineCoordinateMap K)
      (NativeDominantFunctionField.map (GrassmannianCharts.chartSpecMap K 4 6 pivotEmbedding) z)) = _
  rw [affine_pullback_eq]
  congr 1

instance actualFieldAlgebra : Algebra
    (GrassmannianCharts.space K 4 6).functionField (ConicFrameProjective.space K).functionField :=
  (functionFieldEmbedding K).toRingHom.toAlgebra

/-- Dimensions of the two extensions agree because the genuine embedding
square was proved above. -/
theorem native_finrank_eq :
    Module.finrank (GrassmannianCharts.space K 4 6).functionField
      (ConicFrameProjective.space K).functionField =
      Module.finrank (targetField K) (rationalField K) := by
  apply Algebra.finrank_eq_of_equiv_equiv
    (targetNativeEquiv K).toRingEquiv (projectiveNativeEquiv K).toRingEquiv
  apply RingHom.ext
  intro z
  exact (embedding_comparison K z).symm

end M9Native.ConicFrameFieldComparison

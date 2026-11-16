module

public import M9StacksIntegration.ConicFramePairFixedField

/-! The literal native product symmetry induces the original independent
frame-variable swap through the proved pair conic-cover fixed field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace M9Native.ConicFramePairSwap

open ConicFramePairRings ConicFrameSourceAlgebra ConicFramePairFixedField

abbrev A := targetPair ℂ
abbrev B := sourcePair ℂ
abbrev TargetField := targetPairField ℂ

def targetSwap : TargetField ≃ₐ[ℂ] TargetField :=
  IsFractionRing.algEquivOfAlgEquiv (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ))

def sourceSwap : SourceField ≃ₐ[ℂ] SourceField :=
  IsFractionRing.algEquivOfAlgEquiv (Algebra.TensorProduct.comm ℂ (sourceRing ℂ) (sourceRing ℂ))

@[simp] theorem targetSwap_algebraMap (a : A) :
    targetSwap (algebraMap A TargetField a) =
      algebraMap A TargetField (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ) a) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ a

@[simp] theorem sourceSwap_algebraMap (b : B) :
    sourceSwap (algebraMap B SourceField b) =
      algebraMap B SourceField (Algebra.TensorProduct.comm ℂ (sourceRing ℂ) (sourceRing ℂ) b) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ b

theorem coordinatePairMap_swap (a : A) :
    coordinatePairMap ℂ (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ) a) =
      Algebra.TensorProduct.comm ℂ (sourceRing ℂ) (sourceRing ℂ) (coordinatePairMap ℂ a) := by
  induction a using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem pairFieldEmbedding_swap (x : TargetField) :
    pairFieldEmbedding ℂ (targetSwap x) = sourceSwap (pairFieldEmbedding ℂ x) := by
  have h : (pairFieldEmbedding ℂ).toRingHom.comp targetSwap.toRingHom =
      sourceSwap.toRingHom.comp (pairFieldEmbedding ℂ).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    change pairFieldEmbedding ℂ (targetSwap (algebraMap A TargetField a)) =
      sourceSwap (pairFieldEmbedding ℂ (algebraMap A TargetField a))
    rw [targetSwap_algebraMap, pairFieldEmbedding_algebraMap,
      pairFieldEmbedding_algebraMap, sourceSwap_algebraMap, coordinatePairMap_swap]
  exact DFunLike.congr_fun h x

theorem sourceToNested_swap (x : SourceField) :
    sourceToNested (sourceSwap x) =
      ConicFrameIndependentPairAction.swap (sourceToNested x) := by
  have h : sourceToNested.toRingHom.comp sourceSwap.toRingHom =
      ConicFrameIndependentPairAction.swap.toRingHom.comp sourceToNested.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := B)
    intro b
    change sourceToNested (sourceSwap (algebraMap B SourceField b)) =
      ConicFrameIndependentPairAction.swap (sourceToNested (algebraMap B SourceField b))
    induction b using TensorProduct.inductionOn with
    | tmul b c =>
      rw [sourceSwap_algebraMap, Algebra.TensorProduct.comm_tmul,
        sourceToNested_tmul, sourceToNested_tmul, map_mul,
        ConicFrameIndependentPairAction.swap_coefficient,
        ConicFrameIndependentPairAction.swap_outer]
      exact mul_comm _ _
    | add b c hb hc => simp only [map_add, hb, hc]
  exact DFunLike.congr_fun h x

/-- The actual symmetry of the native product Grassmannian. -/
def schemeSwap : ConicFramePairFieldComparison.target ≅ ConicFramePairFieldComparison.target :=
  pullbackSymmetry (GrassmannianCharts.projection ℂ 4 6) (GrassmannianCharts.projection ℂ 4 6)

instance schemeSwap_isDominant : IsDominant schemeSwap.hom :=
  ⟨schemeSwap.hom.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem schemeSwap_over :
    schemeSwap.hom ≫ GrassmannianProductCharts.productProjection ℂ 4 6 =
      GrassmannianProductCharts.productProjection ℂ 4 6 := by
  change (pullbackSymmetry _ _).hom ≫ (pullback.fst _ _ ≫ _) = _
  rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pullback.condition.symm

/-- Pullback by the literal product symmetry on the actual native generic stalk. -/
def nativeSwap : grassmannianPairField ≃ₐ[ℂ] grassmannianPairField := by
  let e := GrassmannianCharts.openImmersionFunctionFieldIso schemeSwap.hom
  refine { __ := e.commRingCatIsoToRingEquiv, commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar ℂ schemeSwap.hom
    (GrassmannianProductCharts.productProjection ℂ 4 6)
  rw [schemeSwap_over] at h
  exact DFunLike.congr_fun h c

theorem nativeSwap_eq_map : nativeSwap.toRingHom = NativeDominantFunctionField.map schemeSwap.hom :=
  ConicFrameFieldComparison.openIso_eq_map schemeSwap.hom

def affineSwap : Spec (.of A) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ)).toRingHom)

instance affineSwap_isIso : IsIso affineSwap := by
  unfold affineSwap
  have : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ)).toRingHom) :=
    (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ)).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

instance affineSwap_isDominant : IsDominant affineSwap :=
  ⟨affineSwap.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem targetChart_swap :
    affineSwap ≫ ConicFramePairFieldComparison.targetChart =
      ConicFramePairFieldComparison.targetChart ≫ schemeSwap.hom := by
  change affineSwap ≫ GrassmannianProductCharts.chartSpecMap ℂ 4 6
      ConicFrameCoordinateIndex.pivotEmbedding ConicFrameCoordinateIndex.pivotEmbedding =
    GrassmannianProductCharts.chartSpecMap ℂ 4 6
      ConicFrameCoordinateIndex.pivotEmbedding ConicFrameCoordinateIndex.pivotEmbedding ≫
        (pullbackSymmetry _ _).hom
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      GrassmannianProductCharts.chartSpecMap_fst, GrassmannianProductCharts.chartSpecMap_snd]
    rw [← Category.assoc, affineSwap, ← Spec.map_comp]
    rfl
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      GrassmannianProductCharts.chartSpecMap_fst, GrassmannianProductCharts.chartSpecMap_snd]
    rw [← Category.assoc, affineSwap, ← Spec.map_comp]
    rfl

def affineFractionEquiv : (Spec (.of A)).functionField ≃ₐ[A] TargetField :=
  (FractionRing.algEquiv A (Spec (.of A)).functionField).symm

theorem affineSwap_pullback (z : (Spec (.of A)).functionField) :
    affineFractionEquiv (NativeDominantFunctionField.map affineSwap z) =
      targetSwap (affineFractionEquiv z) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ)).toRingHom)) :=
    affineSwap_isDominant
  have h : affineFractionEquiv.toRingHom.comp (NativeDominantFunctionField.map affineSwap) =
      targetSwap.toRingHom.comp affineFractionEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    change affineFractionEquiv
      (NativeDominantFunctionField.map (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.comm ℂ (targetRing ℂ) (targetRing ℂ)).toRingHom))
          (algebraMap A (Spec (.of A)).functionField a)) =
      targetSwap (affineFractionEquiv (algebraMap A (Spec (.of A)).functionField a))
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, affineFractionEquiv.commutes,
      affineFractionEquiv.commutes, targetSwap_algebraMap]
    rfl
  exact DFunLike.congr_fun h z

theorem targetNativeEquiv_apply (z : grassmannianPairField) :
    ConicFramePairFieldComparison.targetNativeEquiv z =
      affineFractionEquiv (NativeDominantFunctionField.map ConicFramePairFieldComparison.targetChart z) := by
  rw [← ConicFrameFieldComparison.openIso_eq_map ConicFramePairFieldComparison.targetChart]
  rfl

theorem targetNativeEquiv_swap (z : grassmannianPairField) :
    ConicFramePairFieldComparison.targetNativeEquiv (nativeSwap z) =
      targetSwap (ConicFramePairFieldComparison.targetNativeEquiv z) := by
  have h := ConicFrameNativeActionCoordinates.map_congr targetChart_swap
  rw [NativeFunctionFieldFunctor.map_comp, NativeFunctionFieldFunctor.map_comp] at h
  have hz := DFunLike.congr_fun h z
  change NativeDominantFunctionField.map affineSwap
      (NativeDominantFunctionField.map ConicFramePairFieldComparison.targetChart z) =
    NativeDominantFunctionField.map ConicFramePairFieldComparison.targetChart
      (NativeDominantFunctionField.map schemeSwap.hom z) at hz
  rw [targetNativeEquiv_apply, targetNativeEquiv_apply]
  change affineFractionEquiv (NativeDominantFunctionField.map ConicFramePairFieldComparison.targetChart
    (nativeSwap.toRingHom z)) = _
  rw [nativeSwap_eq_map, ← hz, affineSwap_pullback]

/-- The actual native factor swap is intertwined with the literal
independent frame-variable swap. -/
theorem embedding_swap (z : grassmannianPairField) :
    functionFieldEmbedding (nativeSwap z) =
      ConicFrameIndependentPairAction.swap (functionFieldEmbedding z) := by
  change sourceToNested (pairFieldEmbedding ℂ
    (ConicFramePairFieldComparison.targetNativeEquiv (nativeSwap z))) = _
  rw [targetNativeEquiv_swap, pairFieldEmbedding_swap, sourceToNested_swap]
  rfl

theorem involution_of_intertwining {k L M : Type*} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] (f : L →ₐ[k] M)
    (s : L ≃ₐ[k] L) (t : M ≃ₐ[k] M) (h : ∀ z, f (s z) = t (f z))
    (ht : t * t = 1) : s * s = 1 := by
  apply AlgEquiv.ext
  intro z
  apply f.injective
  change f (s (s z)) = f z
  rw [h, h]
  exact congrArg (fun e : M ≃ₐ[k] M => e (f z)) ht

theorem nativeSwap_squared : nativeSwap * nativeSwap = 1 :=
  involution_of_intertwining functionFieldEmbedding nativeSwap
    ConicFrameIndependentPairAction.swap embedding_swap
    ConicFrameIndependentPairAction.swap_squared

def fixedSwap : fixedField ≃ₐ[ℂ] fixedField :=
  nativeGrassmannianPairFixedFieldEquiv.symm.trans
    (nativeSwap.trans nativeGrassmannianPairFixedFieldEquiv)

theorem fixedSwap_equivariant (z : grassmannianPairField) :
    fixedSwap (nativeGrassmannianPairFixedFieldEquiv z) =
      nativeGrassmannianPairFixedFieldEquiv (nativeSwap z) := by
  simp only [fixedSwap, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

theorem fixedSwap_coe (x : fixedField) :
    (fixedSwap x : PairField) = ConicFrameIndependentPairAction.swap (x : PairField) := by
  obtain ⟨z,rfl⟩ := nativeGrassmannianPairFixedFieldEquiv.surjective x
  rw [fixedSwap_equivariant, nativeGrassmannianPairFixedFieldEquiv_coe,
    nativeGrassmannianPairFixedFieldEquiv_coe]
  exact embedding_swap z

end M9Native.ConicFramePairSwap

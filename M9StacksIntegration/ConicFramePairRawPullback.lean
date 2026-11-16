module

public import M9StacksIntegration.ConicFrameLeftEquivariance
public import M9StacksIntegration.ConicFramePairFixedField
public import M9StacksIntegration.PairProjectiveEquivariance

/-! The actual native product-conic pullback inside the original independent
frame field. The generic test morphism retains the two original matrices;
its equality with the named ratio embedding is proved from the real affine
source and generic-stalk pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open scoped TensorProduct

namespace M9Native.ConicFramePairRawPullback

open ConicFramePairRings ConicFrameSourceAlgebra ConicFrameSourceMatrix
open ConicFramePairFixedField
open M9.FrameFieldElimination

abbrev PF := PairProjectiveRatios.PF
abbrev RawSpec : Scheme := Spec (.of PF)
abbrev GrassPair := ConicFramePairFieldComparison.target
abbrev SourceRing := sourcePair ℂ

def rawProjection : RawSpec ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ PF))

def sourceToRaw : SourceField →ₐ[ℂ] PF :=
  PairProjectiveRatios.pairRatioEmbedding.comp sourceToNested.toAlgHom

def sourceRingToRaw : SourceRing →ₐ[ℂ] PF :=
  sourceToRaw.comp (IsScalarTower.toAlgHom ℂ SourceRing SourceField)

def sourcePoint : RawSpec ⟶ ConicFramePairFieldComparison.source :=
  Spec.map (CommRingCat.ofHom sourceRingToRaw.toRingHom)

instance sourcePoint_isDominant : IsDominant sourcePoint :=
  NativeDominantFunctionField.specMap_isDominant _
    (sourceToRaw.injective.comp (IsFractionRing.injective SourceRing SourceField))

/-- The literal actual generic conic-pair point, before any invariant-field
identification. -/
def rawPoint : RawSpec ⟶ GrassPair :=
  sourcePoint ≫ ConicFramePairFieldComparison.conicPairMap

instance rawPoint_isDominant : IsDominant rawPoint := by
  unfold rawPoint
  infer_instance

def rawEmbedding : GrassPair.functionField →ₐ[ℂ] PF :=
  PairProjectiveRatios.pairRatioEmbedding.comp functionFieldEmbedding

/-- The actual generic stalk of the spectrum of a field is that field. -/
def affineFieldEquiv : RawSpec.functionField ≃+* PF :=
  (IsFractionRing.algEquiv PF PF RawSpec.functionField).symm.toRingEquiv

@[simp] theorem affineFieldEquiv_algebraMap (z : PF) :
    affineFieldEquiv (algebraMap PF RawSpec.functionField z) = z := by
  exact (IsFractionRing.algEquiv PF PF RawSpec.functionField).symm.commutes z

theorem sourcePoint_pullback (z : ConicFramePairFieldComparison.source.functionField) :
    affineFieldEquiv (NativeDominantFunctionField.map sourcePoint z) =
      sourceToRaw (ConicFramePairFieldComparison.sourceNativeEquiv z) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom sourceRingToRaw.toRingHom)) :=
    sourcePoint_isDominant
  have hh : affineFieldEquiv.toRingHom.comp (NativeDominantFunctionField.map sourcePoint) =
      sourceToRaw.toRingHom.comp ConicFramePairFieldComparison.sourceNativeEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := SourceRing)
    intro b
    change affineFieldEquiv (NativeDominantFunctionField.map
        (Spec.map (CommRingCat.ofHom sourceRingToRaw.toRingHom))
          (algebraMap SourceRing ConicFramePairFieldComparison.source.functionField b)) = _
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, affineFieldEquiv_algebraMap]
    change sourceRingToRaw b =
      sourceToRaw (ConicFramePairFieldComparison.sourceNativeEquiv
        (algebraMap SourceRing ConicFramePairFieldComparison.source.functionField b))
    rw [ConicFramePairFieldComparison.sourceNativeEquiv_algebraMap]
    rfl
  exact DFunLike.congr_fun hh z

/-- This exact raw frame embedding is the genuine generic-stalk pullback
of the actual product conic morphism. -/
theorem rawEmbedding_eq_pullback (z : GrassPair.functionField) :
    rawEmbedding z = affineFieldEquiv (NativeDominantFunctionField.map rawPoint z) := by
  change rawEmbedding z = affineFieldEquiv (NativeDominantFunctionField.map
    (sourcePoint ≫ ConicFramePairFieldComparison.conicPairMap) z)
  rw [NativeFunctionFieldFunctor.map_comp, RingHom.comp_apply, sourcePoint_pullback]
  change PairProjectiveRatios.pairRatioEmbedding (functionFieldEmbedding z) =
    PairProjectiveRatios.pairRatioEmbedding (sourceToNested
      (ConicFramePairFieldComparison.sourceNativeEquiv
        (NativeDominantFunctionField.map ConicFramePairFieldComparison.conicPairMap z)))
  rw [ConicFramePairFixedField.embedding_comparison]

theorem sourceRingToRaw_left (b : sourceRing ℂ) :
    sourceRingToRaw (b ⊗ₜ[ℂ] 1) =
      PairProjectiveEquivariance.firstBlock (toRationalAlgHom ℂ b) := by
  change PairProjectiveRatios.pairRatioEmbedding
    (sourceToNested (leftSourceEmbedding b)) = _
  rw [← leftFieldEmbedding_toRational, sourceToNested_leftField]
  rfl

theorem sourceRingToRaw_right (b : sourceRing ℂ) :
    sourceRingToRaw (1 ⊗ₜ[ℂ] b) =
      PairProjectiveEquivariance.secondBlock (toRationalAlgHom ℂ b) := by
  change PairProjectiveRatios.pairRatioEmbedding
    (sourceToNested (rightSourceEmbedding b)) = _
  rw [← rightFieldEmbedding_toRational, sourceToNested_rightField]
  rfl

def firstRingMap : sourceRing ℂ →ₐ[ℂ] PF :=
  sourceRingToRaw.comp (Algebra.TensorProduct.includeLeft : sourceRing ℂ →ₐ[ℂ] SourceRing)

def secondRingMap : sourceRing ℂ →ₐ[ℂ] PF :=
  sourceRingToRaw.comp (Algebra.TensorProduct.includeRight : sourceRing ℂ →ₐ[ℂ] SourceRing)

theorem firstRingMap_eq : firstRingMap =
    PairProjectiveEquivariance.firstBlock.comp (toRationalAlgHom ℂ) := by
  apply AlgHom.ext
  exact sourceRingToRaw_left

theorem secondRingMap_eq : secondRingMap =
    PairProjectiveEquivariance.secondBlock.comp (toRationalAlgHom ℂ) := by
  apply AlgHom.ext
  exact sourceRingToRaw_right

theorem firstFrame_normalized :
    (sourceFrame ℂ).map firstRingMap.toRingHom =
      (firstFrame ℂ 0 0)⁻¹ • firstFrame ℂ := by
  rw [firstRingMap_eq]
  change ((sourceFrame ℂ).map (toRationalAlgHom ℂ).toRingHom).map
    PairProjectiveEquivariance.firstBlock.toRingHom = _
  have hf : (sourceFrame ℂ).map (toRationalAlgHom ℂ).toRingHom =
      ConicFrameRationalGamma.genericFrame := by
    ext i j
    change toRational ℂ (algebraMap (ConicFrameProjective.polynomial ℂ) (sourceRing ℂ)
      (ConicFrameProjective.normalizedFrame ℂ i j)) = _
    rw [toRational_algebraMap]
    rfl
  rw [hf]
  exact PairProjectiveEquivariance.genericFrame_map _ _
    (PairProjectiveRatios.firstFrame_ne_zero (0,0)) PairProjectiveEquivariance.firstBlock_variable

theorem secondFrame_normalized :
    (sourceFrame ℂ).map secondRingMap.toRingHom =
      (secondFrame ℂ 0 0)⁻¹ • secondFrame ℂ := by
  rw [secondRingMap_eq]
  change ((sourceFrame ℂ).map (toRationalAlgHom ℂ).toRingHom).map
    PairProjectiveEquivariance.secondBlock.toRingHom = _
  have hf : (sourceFrame ℂ).map (toRationalAlgHom ℂ).toRingHom =
      ConicFrameRationalGamma.genericFrame := by
    ext i j
    change toRational ℂ (algebraMap (ConicFrameProjective.polynomial ℂ) (sourceRing ℂ)
      (ConicFrameProjective.normalizedFrame ℂ i j)) = _
    rw [toRational_algebraMap]
    rfl
  rw [hf]
  exact PairProjectiveEquivariance.genericFrame_map _ _
    (PairProjectiveRatios.secondFrame_ne_zero (0,0)) PairProjectiveEquivariance.secondBlock_variable

/-- Actual globalization of a matrix over the original pair field. -/
def globalize (F : ConicFrame.Mat3 PF) : ConicFrame.Mat3 Γ(RawSpec, ⊤) :=
  F.map (Scheme.ΓSpecIso (.of PF)).inv.hom

theorem globalize_det_unit (F : ConicFrame.Mat3 PF) (hF : IsUnit F.det) :
    IsUnit (globalize F).det := by
  rw [globalize, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hF.map _

theorem firstFrame_det_unit : IsUnit (firstFrame ℂ).det := by
  have h := (ConicFrameSourceMatrix.sourceFrame_det_unit ℂ).map firstRingMap.toRingHom
  rw [RingHom.map_det, RingHom.mapMatrix_apply, firstFrame_normalized, Matrix.det_smul] at h
  exact isUnit_of_mul_isUnit_right h

theorem secondFrame_det_unit : IsUnit (secondFrame ℂ).det := by
  have h := (ConicFrameSourceMatrix.sourceFrame_det_unit ℂ).map secondRingMap.toRingHom
  rw [RingHom.map_det, RingHom.mapMatrix_apply, secondFrame_normalized, Matrix.det_smul] at h
  exact isUnit_of_mul_isUnit_right h

def firstConicPoint : RawSpec ⟶ GrassmannianCharts.space ℂ 4 6 :=
  ConicFrame.map RawSpec ℂ rawProjection (globalize (firstFrame ℂ))
    (globalize_det_unit _ firstFrame_det_unit)

def secondConicPoint : RawSpec ⟶ GrassmannianCharts.space ℂ 4 6 :=
  ConicFrame.map RawSpec ℂ rawProjection (globalize (secondFrame ℂ))
    (globalize_det_unit _ secondFrame_det_unit)

theorem sourcePoint_left : sourcePoint ≫ ConicFramePairFieldComparison.leftSourceProjection =
    Spec.map (CommRingCat.ofHom firstRingMap.toRingHom) := by
  rw [sourcePoint, ConicFramePairFieldComparison.leftSourceProjection, ← Spec.map_comp]
  rfl

theorem sourcePoint_right : sourcePoint ≫ ConicFramePairFieldComparison.rightSourceProjection =
    Spec.map (CommRingCat.ofHom secondRingMap.toRingHom) := by
  rw [sourcePoint, ConicFramePairFieldComparison.rightSourceProjection, ← Spec.map_comp]
  rfl

theorem globalFrame_pullback (φ : sourceRing ℂ →ₐ[ℂ] PF) :
    (ConicFrameNativeGeometry.globalFrame ℂ).map
        (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop.hom =
      globalize ((sourceFrame ℂ).map φ.toRingHom) := by
  ext i j
  change (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv (sourceFrame ℂ i j)) =
    (Scheme.ΓSpecIso (.of PF)).inv (φ (sourceFrame ℂ i j))
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem sourceProjection_pullback (φ : sourceRing ℂ →ₐ[ℂ] PF) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ConicFrameNativeGeometry.sourceProjection ℂ =
      rawProjection := by
  rw [ConicFrameNativeGeometry.sourceProjection, rawProjection, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom φ.comp_algebraMap

theorem conicPoint_pullback (φ : sourceRing ℂ →ₐ[ℂ] PF) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ConicFrameNativeGeometry.conicMap ℂ =
      ConicFrame.map RawSpec ℂ rawProjection (globalize ((sourceFrame ℂ).map φ.toRingHom))
        (globalize_det_unit _ (by
          rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
          exact (ConicFrameSourceMatrix.sourceFrame_det_unit ℂ).map _)) := by
  rw [ConicFrameNativeGeometry.conicMap_eq_classifying]
  have hu : IsUnit ((ConicFrameNativeGeometry.globalFrame ℂ).map
      (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop.hom).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (ConicFrameNativeGeometry.globalFrame_det_unit ℂ).map _
  rw [ConicFrameLeftEquivariance.map_natural ℂ _ _ _ _ hu, sourceProjection_pullback]
  simp only [globalFrame_pullback]

theorem globalize_smul (c : PF) (F : ConicFrame.Mat3 PF) :
    globalize (c • F) = (Scheme.ΓSpecIso (.of PF)).inv c • globalize F := by
  ext i j
  exact (Scheme.ΓSpecIso (.of PF)).inv.hom.map_mul c (F i j)

theorem map_globalize_smul (c : PF) (hc : c ≠ 0) (F : ConicFrame.Mat3 PF)
    (hF : IsUnit F.det) (hF' : IsUnit (globalize (c • F)).det) :
    ConicFrame.map RawSpec ℂ rawProjection (globalize (c • F)) hF' =
      ConicFrame.map RawSpec ℂ rawProjection (globalize F) (globalize_det_unit F hF) := by
  let cu : Γ(RawSpec, ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (.of PF)).inv.hom.toMonoidHom (Units.mk0 c hc)
  have hh : globalize (c • F) = (cu : Γ(RawSpec, ⊤)) • globalize F := globalize_smul c F
  have hFc : IsUnit (((cu : Γ(RawSpec, ⊤)) • globalize F).det) := hh ▸ hF'
  have he := ConicFrame.map_smul RawSpec ℂ rawProjection (globalize F)
    (globalize_det_unit F hF) cu hFc
  simpa only [← hh] using he.symm

/-- The first actual original frame, including its original scalar, gives
the first component of the native generic conic-pair point. -/
theorem rawPoint_fst : rawPoint ≫ pullback.fst _ _ = firstConicPoint := by
  rw [rawPoint, Category.assoc, ConicFramePairFieldComparison.conicPairMap_fst,
    ← Category.assoc, sourcePoint_left, conicPoint_pullback]
  have he := firstFrame_normalized
  simp only [he]
  exact map_globalize_smul _ (inv_ne_zero (PairProjectiveRatios.firstFrame_ne_zero (0,0)))
    (firstFrame ℂ) firstFrame_det_unit _

theorem rawPoint_snd : rawPoint ≫ pullback.snd _ _ = secondConicPoint := by
  rw [rawPoint, Category.assoc, ConicFramePairFieldComparison.conicPairMap_snd,
    ← Category.assoc, sourcePoint_right, conicPoint_pullback]
  have he := secondFrame_normalized
  simp only [he]
  exact map_globalize_smul _ (inv_ne_zero (PairProjectiveRatios.secondFrame_ne_zero (0,0)))
    (secondFrame ℂ) secondFrame_det_unit _

end M9Native.ConicFramePairRawPullback

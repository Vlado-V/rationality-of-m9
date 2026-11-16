module

public import M9StacksIntegration.NativeDenseSchemeFunctionField
public import M9StacksIntegration.PrimitiveGrassmannianAction
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Projective

@[expose] public section

/-! Restrict an actual native dense classifier on an actual open of the
original complex Gr9(14) to an actual represented open chart of its target.
The new Grassmannian open, its map to the chart, dominance and the original
coefficient base square are derived from the actual native pullback.
No quotient-field identification or geometric orbit condition is asserted. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] Space.pointTopology

namespace M9Native.PrimitiveNativeDenseChartPresentation

open PrimitiveGrassmannianAction
  M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalPullbacks
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalSchemes

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ)))

include hC in
/-- Every original Gr9 open is in the same site as the original complex
field. Its membership is derived from actual projectivity and openness. -/
theorem contains_parameter_open (U : space.Opens) : B.Contains U.toScheme := by
  let : IsProper projection := isProper_of_isProjectiveMorphism _
    (Grassmannian.isProjectiveMorphism_schemeOver 9 14 (Spec (.of ℂ)))
  have hP : B.Contains space :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact projection hC
  exact Scheme.size_lt_of_isOpenImmersion U.ι hP

/-- The SAME original Grassmannian open, with its original complex map. -/
def parameterObject (U : space.Opens) : BigFppfOver B (Spec (.of ℂ)) hC :=
  siteObject B (Spec (.of ℂ)) hC (contains_parameter_open B hC U) (U.ι ≫ projection)

variable (M : AlgebraicSpaces B (Spec (.of ℂ)) hC) (U : space.Opens)
  (f : yoneda.obj (parameterObject B hC U) ⟶ M.obj)
  (V : BigFppfOver B (Spec (.of ℂ)) hC) (j : yoneda.obj V ⟶ M.obj)
  (hj : Space.IsOpenImmersion B (Spec (.of ℂ)) hC j)

/-- The actual representing object of the actual classifier/chart pullback. -/
def pullbackObject : BigFppfOver B (Spec (.of ℂ)) hC := hj.rep.pullback f

def pullbackToSource : pullbackObject B hC M U f V j hj ⟶ parameterObject B hC U :=
  hj.rep.snd f

def pullbackToChart : pullbackObject B hC M U f V j hj ⟶ V :=
  yoneda.preimage (hj.rep.fst f)

/-- Both literal original native classifier maps occur in this pullback. -/
theorem nativePullback :
    IsPullback (yoneda.map (pullbackToChart B hC M U f V j hj))
      (yoneda.map (pullbackToSource B hC M U f V j hj)) j f := by
  rw [pullbackToChart, yoneda.map_preimage]
  exact hj.rep.isPullback f

instance pullbackToSource_isOpenImmersion :
    IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
      (pullbackToSource B hC M U f V j hj)) :=
  hj.property_snd f

/-- The actual open immersion of the representing pullback into Gr9. -/
def parameterMap :
    (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj
      (pullbackObject B hC M U f V j hj) ⟶ space :=
  (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
    (pullbackToSource B hC M U f V j hj) ≫ U.ι

instance parameterMap_isOpenImmersion :
    IsOpenImmersion (parameterMap B hC M U f V j hj) := by
  unfold parameterMap
  infer_instance

/-- The smaller open is the ACTUAL image of the actual pullback immersion. -/
def restrictedOpen : space.Opens := (parameterMap B hC M U f V j hj).opensRange

theorem restrictedOpen_le : restrictedOpen B hC M U f V j hj ≤ U := by
  intro x hx
  change x ∈ Set.range (parameterMap B hC M U f V j hj) at hx
  obtain ⟨p, rfl⟩ := hx
  exact ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
    (pullbackToSource B hC M U f V j hj) p).property

/-- The actual representing scheme is isomorphic to its actual Gr9 image. -/
def parameterIso :
    (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj
        (pullbackObject B hC M U f V j hj) ≅
      (restrictedOpen B hC M U f V j hj).toScheme :=
  (parameterMap B hC M U f V j hj).isoOpensRange

/-- The retained source map is the canonical inclusion of the smaller open. -/
theorem parameterIso_inverse_toSource :
    (parameterIso B hC M U f V j hj).inv ≫
        (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
          (pullbackToSource B hC M U f V j hj) =
      space.homOfLE (restrictedOpen_le B hC M U f V j hj) := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, ← parameterMap]
  exact (Scheme.Hom.isoOpensRange_inv_comp (parameterMap B hC M U f V j hj)).trans
    (Scheme.homOfLE_ι space (restrictedOpen_le B hC M U f V j hj)).symm

/-- The ordinary scheme map is produced by the actual pullback and image iso. -/
def mapToChart :
    (restrictedOpen B hC M U f V j hj).toScheme ⟶
      (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V :=
  (parameterIso B hC M U f V j hj).inv ≫
    (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
      (pullbackToChart B hC M U f V j hj)

/-- The actual original complex structure morphism is preserved. -/
theorem mapToChart_over_base :
    mapToChart B hC M U f V j hj ≫ B.inclusion.map V.hom =
      (restrictedOpen B hC M U f V j hj).ι ≫ projection := by
  have hv := congrArg B.inclusion.map
    (Over.w (pullbackToChart B hC M U f V j hj))
  have hu := congrArg B.inclusion.map
    (Over.w (pullbackToSource B hC M U f V j hj))
  rw [Functor.map_comp] at hv hu
  change (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
      (pullbackToChart B hC M U f V j hj) ≫ B.inclusion.map V.hom = _ at hv
  change (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
      (pullbackToSource B hC M U f V j hj) ≫ (U.ι ≫ projection) = _ at hu
  change (parameterIso B hC M U f V j hj).inv ≫
    ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
      (pullbackToChart B hC M U f V j hj) ≫ B.inclusion.map V.hom) = _
  rw [hv, ← hu, ← Category.assoc, parameterIso_inverse_toSource,
    ← Category.assoc, Scheme.homOfLE_ι]

/-- The genuine native classifier density produces ordinary pullback density. -/
theorem pullbackToChart_dense
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (parameterObject B hC U)) f)) :
    DenseRange ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
      (pullbackToChart B hC M U f V j hj)) :=
  M9StacksIntegration.NativeDenseChartPullback.denseRange_toScheme_of_isPullback
    B (Spec (.of ℂ)) hC f (yoneda.map (pullbackToSource B hC M U f V j hj))
    (pullbackToChart B hC M U f V j hj) j
    (nativePullback B hC M U f V j hj).flip
    (M9StacksIntegration.NativeIntegralDenseScheme.etale_of_open ℂ B hC V j hj) hf

/-- Dominance of the actual ordinary q is a conclusion, not an input. -/
theorem mapToChart_dense
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (parameterObject B hC U)) f)) :
    DenseRange (mapToChart B hC M U f V j hj) := by
  change Dense (Set.range ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
    (pullbackToChart B hC M U f V j hj) ∘ (parameterIso B hC M U f V j hj).inv))
  rw [(parameterIso B hC M U f V j hj).inv.surjective.range_comp]
  exact pullbackToChart_dense B hC M U f V j hj hf

theorem mapToChart_isDominant
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (parameterObject B hC U)) f)) :
    IsDominant (mapToChart B hC M U f V j hj) :=
  ⟨mapToChart_dense B hC M U f V j hj hf⟩

include hj in
/-- Native integrality and the actual dense chart derive chart integrality. -/
theorem chart_isIntegral
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC M.obj)
    (hdj : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC (yoneda.obj V) j)) :
    IsIntegral ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V) :=
  M9StacksIntegration.NativeIntegralDenseScheme.scheme_isIntegral_of_dense_open
    ℂ B hC M hInt.1 hInt.2.2 V j hj hdj

/-- The smaller ACTUAL Gr9 open is nonempty by the derived dominant map
to the actual integral chart; no chosen parameter point is assumed. -/
theorem restrictedOpen_nonempty
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC M.obj)
    (hdj : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC (yoneda.obj V) j))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (parameterObject B hC U)) f)) :
    Nonempty (restrictedOpen B hC M U f V j hj) := by
  have := chart_isIntegral B hC M V j hj hInt hdj
  exact (mapToChart_dense B hC M U f V j hj hf).nonempty_iff.mpr inferInstance

/-- The actual derived q as an arrow over the original complex field. -/
def mapOver :
    Over.mk ((restrictedOpen B hC M U f V j hj).ι ≫ projection) ⟶
      (boundedInclusion B ℂ hC).obj V :=
  Over.homMk (mapToChart B hC M U f V j hj)
    (mapToChart_over_base B hC M U f V j hj)

/-- The image isomorphism retains the original complex structure map. -/
def originalParameterIso :
    (boundedInclusion B ℂ hC).obj (pullbackObject B hC M U f V j hj) ≅
      Over.mk ((restrictedOpen B hC M U f V j hj).ι ≫ projection) :=
  Over.isoMk (parameterIso B hC M U f V j hj) (by
    have hu := congrArg B.inclusion.map
      (Over.w (pullbackToSource B hC M U f V j hj))
    rw [Functor.map_comp] at hu
    change (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).map
      (pullbackToSource B hC M U f V j hj) ≫ (U.ι ≫ projection) = _ at hu
    have he : (parameterIso B hC M U f V j hj).hom ≫
        (restrictedOpen B hC M U f V j hj).ι = parameterMap B hC M U f V j hj :=
      Scheme.Hom.isoOpensRange_hom_ι (parameterMap B hC M U f V j hj)
    change (parameterIso B hC M U f V j hj).hom ≫
      ((restrictedOpen B hC M U f V j hj).ι ≫ projection) = _
    rw [← Category.assoc, he, parameterMap, Category.assoc]
    exact hu)

/-- The source map on the original site is the canonical smaller-open inclusion. -/
def inclusionOver :
    Over.mk ((restrictedOpen B hC M U f V j hj).ι ≫ projection) ⟶
      (boundedInclusion B ℂ hC).obj (parameterObject B hC U) :=
  Over.homMk (space.homOfLE (restrictedOpen_le B hC M U f V j hj)) (by
    change space.homOfLE (restrictedOpen_le B hC M U f V j hj) ≫
      (U.ι ≫ projection) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

/-- The literal native pullback becomes the SAME actual pullback on all
original test schemes, retaining both original classifier maps. -/
theorem originalNativePullback :
    IsPullback
      (yoneda.map ((boundedInclusion B ℂ hC).map (pullbackToChart B hC M U f V j hj)))
      (yoneda.map ((boundedInclusion B ℂ hC).map (pullbackToSource B hC M U f V j hj)))
      (originalChart ℂ B hC M V j)
      (originalChart ℂ B hC M (parameterObject B hC U) f) := by
  have hp := original_isPullback ℂ B hC
    (schemeSpaceMap (pullbackToChart B hC M U f V j hj))
    (schemeSpaceMap (pullbackToSource B hC M U f V j hj))
    (ObjectProperty.homMk j : schemeSpace V ⟶ M)
    (ObjectProperty.homMk f : schemeSpace (parameterObject B hC U) ⟶ M)
    (nativePullback B hC M U f V j hj)
  apply hp.of_iso
    (originalSchemeIso ℂ B hC (pullbackObject B hC M U f V j hj))
    (originalSchemeIso ℂ B hC V)
    (originalSchemeIso ℂ B hC (parameterObject B hC U)) (Iso.refl _)
  · exact originalSchemeIso_naturality ℂ B hC (pullbackToChart B hC M U f V j hj)
  · exact originalSchemeIso_naturality ℂ B hC (pullbackToSource B hC M U f V j hj)
  · simp [originalChart]
  · simp [originalChart]

/-- The derived ACTUAL q and canonical inclusion of W form the original
classifier pullback on EVERY original test, including unbounded fields. -/
theorem originalPullback :
    IsPullback (yoneda.map (mapOver B hC M U f V j hj))
      (yoneda.map (inclusionOver B hC M U f V j hj))
      (originalChart ℂ B hC M V j)
      (originalChart ℂ B hC M (parameterObject B hC U) f) := by
  apply (originalNativePullback B hC M U f V j hj).of_iso'
    (yoneda.mapIso (originalParameterIso B hC M U f V j hj).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change yoneda.map (originalParameterIso B hC M U f V j hj).inv ≫
        yoneda.map ((boundedInclusion B ℂ hC).map (pullbackToChart B hC M U f V j hj)) =
      yoneda.map (mapOver B hC M U f V j hj)
    rw [← Functor.map_comp]
    congr 1
  · change yoneda.map (originalParameterIso B hC M U f V j hj).inv ≫
        yoneda.map ((boundedInclusion B ℂ hC).map (pullbackToSource B hC M U f V j hj)) =
      yoneda.map (inclusionOver B hC M U f V j hj)
    rw [← Functor.map_comp]
    congr 1
    apply Over.OverMorphism.ext
    exact parameterIso_inverse_toSource B hC M U f V j hj
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The literal original classifier square, extracted from its actual pullback. -/
theorem originalClassifier_square :
    yoneda.map (mapOver B hC M U f V j hj) ≫ originalChart ℂ B hC M V j =
      yoneda.map (inclusionOver B hC M U f V j hj) ≫
        originalChart ℂ B hC M (parameterObject B hC U) f :=
  (originalPullback B hC M U f V j hj).w

/-- The complete derived presentation retains the original C base and
literal all-test classifier pullback, with no supplied q or dominance. -/
theorem presentation
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC M.obj)
    (hdj : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC (yoneda.obj V) j))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (parameterObject B hC U)) f)) :
    IsIntegral ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V) ∧
      restrictedOpen B hC M U f V j hj ≤ U ∧
      Nonempty (restrictedOpen B hC M U f V j hj) ∧
      IsDominant (mapToChart B hC M U f V j hj) ∧
      mapToChart B hC M U f V j hj ≫ B.inclusion.map V.hom =
        (restrictedOpen B hC M U f V j hj).ι ≫ projection ∧
      IsPullback (yoneda.map (mapOver B hC M U f V j hj))
        (yoneda.map (inclusionOver B hC M U f V j hj))
        (originalChart ℂ B hC M V j)
        (originalChart ℂ B hC M (parameterObject B hC U) f) :=
  ⟨chart_isIntegral B hC M V j hj hInt hdj,
    restrictedOpen_le B hC M U f V j hj,
    restrictedOpen_nonempty B hC M U f V j hj hInt hdj hf,
    mapToChart_isDominant B hC M U f V j hj hf,
    mapToChart_over_base B hC M U f V j hj,
    originalPullback B hC M U f V j hj⟩

end M9Native.PrimitiveNativeDenseChartPresentation

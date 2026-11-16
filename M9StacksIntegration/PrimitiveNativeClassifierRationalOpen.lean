module

public import M9StacksIntegration.PrimitiveNativeDenseChartPresentation
public import M9StacksIntegration.PrimitiveGeometricQuotientRationalOpen

@[expose] public section

/-! A genuine native classifier criterion for actual original rationality.
Only native density/integrality/local finite type and geometric conditions
on the literal all-original classifier are inputs. The dense chart, variety,
ordinary dominant quotient map and its geometry are constructed. This is an
intermediate criterion, not an assertion of these inputs for actual M9. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
attribute [local instance] Space.pointTopology

namespace M9Native.PrimitiveNativeClassifierRationalOpen

open PrimitiveGrassmannianAction PrimitiveGenericOpenPoints
  PrimitiveUniversalFieldAction PrimitiveUniversalExtensionPoints
  M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalPullbacks

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ)))
  (X : AlgebraicSpaces B (Spec (.of ℂ)) hC) (U : space.Opens)
  (f : yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U) ⟶ X.obj)

/-- The native source recovers the SAME original open over the SAME C base. -/
theorem parameterObject_original :
    (boundedInclusion B ℂ hC).obj
        (PrimitiveNativeDenseChartPresentation.parameterObject B hC U) = openOver U := rfl

/-- The literal original classifier, without a pointwise replacement. -/
def originalClassifier :
    yoneda.obj (openOver U) ⟶ (originalPresheafFunctor ℂ B hC).obj X :=
  originalChart ℂ B hC X (PrimitiveNativeDenseChartPresentation.parameterObject B hC U) f

/-- Exact geometric obligations on the actual original classifier.
No quotient map, chart, function-field equality or rationality occurs. -/
structure ClassifierGeometry : Prop where
  constant_invariant : ∀ (T : Over PrimitiveFamilyFreeAction.base)
    (x y : T ⟶ openOver U) (g : PrimitiveConstantFieldAction.Sp6),
    x ≫ inclusionOver U ≫ PrimitiveConstantFieldAction.overMap g = y ≫ inclusionOver U →
      (originalClassifier B hC X U f).app (op T) x =
        (originalClassifier B hC X U f).app (op T) y
  geometric_orbit_fibers : ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra ℂ L]
    (x y : overField L ⟶ openOver U),
    (originalClassifier B hC X U f).app (op (overField L)) x =
        (originalClassifier B hC X U f).app (op (overField L)) y →
      ∃ g : M9.PrimitiveStabilizer.Sp6 L,
        (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
          (x ≫ inclusionOver U) ≫ nativeAction.act).left = (y ≫ inclusionOver U).left

/-- A genuine represented original dense open is monomorphic on all tests. -/
theorem mono_of_denseOpen {Y : M9StandaloneDraft.Schemes ℂ}
    {F : M9StandaloneDraft.Presheaves ℂ} (j : yoneda.obj Y ⟶ F)
    (hj : M9StandaloneDraft.DenseOpen ℂ j) : Mono j := by
  apply MorphismProperty.presheaf_mono_of_le
    (P := MorphismProperty.inverseImage (@IsOpenImmersion)
      (Over.forget (M9StandaloneDraft.Base ℂ))) _ hj.1
  intro A D a ha
  have : IsOpenImmersion a.left := ha
  exact (Over.forget (M9StandaloneDraft.Base ℂ)).mono_of_mono_map
    (inferInstanceAs (Mono a.left))

variable (V : BigFppfOver B (Spec (.of ℂ)) hC) (j : yoneda.obj V ⟶ X.obj)
  (hj : Space.IsOpenImmersion B (Spec (.of ℂ)) hC j)

/-- The canonical inclusion of the actual smaller source, over original C. -/
def restrictedInclusion :
    openOver (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj) ⟶
      openOver U :=
  PrimitiveNativeDenseChartPresentation.inclusionOver B hC X U f V j hj

theorem restrictedInclusion_ambient :
    restrictedInclusion B hC X U f V j hj ≫ inclusionOver U =
      inclusionOver (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj) := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι space
    (PrimitiveNativeDenseChartPresentation.restrictedOpen_le B hC X U f V j hj)

theorem restrictedPoint_ambient (T : Over PrimitiveFamilyFreeAction.base)
    (x : T ⟶ openOver (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj)) :
    (x ≫ restrictedInclusion B hC X U f V j hj) ≫ inclusionOver U =
      x ≫ inclusionOver (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj) := by
  rw [Category.assoc, restrictedInclusion_ambient]

/-- The actual q/classifier square computes each ORIGINAL classifier value. -/
theorem restricted_classifier_value (T : Over PrimitiveFamilyFreeAction.base)
    (x : T ⟶ openOver (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj)) :
    (originalChart ℂ B hC X V j).app (op T)
        (x ≫ PrimitiveNativeDenseChartPresentation.mapOver B hC X U f V j hj) =
      (originalClassifier B hC X U f).app (op T)
        (x ≫ restrictedInclusion B hC X U f V j hj) := by
  have h := NatTrans.congr_app
    (PrimitiveNativeDenseChartPresentation.originalClassifier_square B hC X U f V j hj) (op T)
  exact congrArg (fun a => a x) h

/-- Geometry of the actual classifier transfers to the actual DERIVED q.
Monomorphy of the original chart is derived from its genuine dense open. -/
theorem restrictedGeometry
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC X.obj)
    (hdj : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC (yoneda.obj V) j))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : ClassifierGeometry B hC X U f) :
    letI := PrimitiveNativeDenseChartPresentation.chart_isIntegral B hC X V j hj hInt hdj
    letI := PrimitiveNativeDenseChartPresentation.restrictedOpen_nonempty B hC X U f V j hj hInt hdj hf
    letI := PrimitiveNativeDenseChartPresentation.mapToChart_isDominant B hC X U f V j hj hf
    PrimitiveGeometricQuotientField.Geometry
      (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj)
      (B.inclusion.map V.hom)
      (PrimitiveNativeDenseChartPresentation.mapToChart B hC X U f V j hj) := by
  let := PrimitiveNativeDenseChartPresentation.chart_isIntegral B hC X V j hj hInt hdj
  let := PrimitiveNativeDenseChartPresentation.restrictedOpen_nonempty B hC X U f V j hj hInt hdj hf
  let := PrimitiveNativeDenseChartPresentation.mapToChart_isDominant B hC X U f V j hj hf
  refine ⟨PrimitiveNativeDenseChartPresentation.mapToChart_over_base B hC X U f V j hj, ?_, ?_⟩
  · intro T x y g hxy
    let xU := x ≫ restrictedInclusion B hC X U f V j hj
    let yU := y ≫ restrictedInclusion B hC X U f V j hj
    have hx : xU ≫ inclusionOver U = x ≫ inclusionOver _ :=
      restrictedPoint_ambient B hC X U f V j hj T x
    have hy : yU ≫ inclusionOver U = y ≫ inclusionOver _ :=
      restrictedPoint_ambient B hC X U f V j hj T y
    have hxyU : xU ≫ inclusionOver U ≫ PrimitiveConstantFieldAction.overMap g =
        yU ≫ inclusionOver U := by
      rw [← Category.assoc, hx, hy]
      exact hxy
    have hi := h.constant_invariant T xU yU g hxyU
    have : Mono (originalChart ℂ B hC X V j) := mono_of_denseOpen _
      (M9StacksIntegration.NativeDenseSchematicOriginal.originalChart_denseOpen ℂ B hC X V j hj hdj)
    have he : x ≫ PrimitiveNativeDenseChartPresentation.mapOver B hC X U f V j hj =
        y ≫ PrimitiveNativeDenseChartPresentation.mapOver B hC X U f V j hj := by
      apply CategoryTheory.injective_of_mono ((originalChart ℂ B hC X V j).app (op T))
      rw [restricted_classifier_value, restricted_classifier_value]
      exact hi
    exact congrArg (fun z => z.left) he
  · intro L _ _ _ x y hxy
    let xU := x ≫ restrictedInclusion B hC X U f V j hj
    let yU := y ≫ restrictedInclusion B hC X U f V j hj
    have he : x ≫ PrimitiveNativeDenseChartPresentation.mapOver B hC X U f V j hj =
        y ≫ PrimitiveNativeDenseChartPresentation.mapOver B hC X U f V j hj := by
      apply Over.OverMorphism.ext
      exact hxy
    have hi : (originalClassifier B hC X U f).app (op (overField L)) xU =
        (originalClassifier B hC X U f).app (op (overField L)) yU := by
      rw [← restricted_classifier_value, ← restricted_classifier_value, he]
    obtain ⟨g, hg⟩ := h.geometric_orbit_fibers L xU yU hi
    refine ⟨g, ?_⟩
    have hx : xU ≫ inclusionOver U = x ≫ inclusionOver _ :=
      restrictedPoint_ambient B hC X U f V j hj (overField L) x
    have hy : yU ≫ inclusionOver U = y ≫ inclusionOver _ :=
      restrictedPoint_ambient B hC X U f V j hj (overField L) y
    rw [hx, hy] at hg
    exact hg

/-- The SAME actual chart scheme and original structure map form a native variety. -/
def chartVariety
    (hV : IsIntegral ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V))
    (hs : IsSeparated (B.inclusion.map V.hom))
    (hl : LocallyOfFiniteType (B.inclusion.map V.hom))
    (hq : QuasiCompact (B.inclusion.map V.hom)) : Variety ℂ where
  toScheme := (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V
  structureMap := B.inclusion.map V.hom
  isVariety :=
    { toIsIntegral := hV
      toIsSeparated := hs
      toLocallyOfFiniteType := hl
      toQuasiCompact := hq }

/-- Native integral finite-type geometry and actual classifier geometry
derive the literal common dense open of the ACTUAL original space with A24. -/
theorem rationalOpen
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC X.obj)
    (hft : Space.IsLocallyOfFiniteType B (Spec (.of ℂ)) hC
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of ℂ)) hC).from X.obj))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : ClassifierGeometry B hC X U f) :
    M9StandaloneDraft.RationalOpen ℂ 24 ((originalPresheafFunctor ℂ B hC).obj X) := by
  obtain ⟨V, j, hV, hA, hs, hl, hq, hj, hdj, hjo, _⟩ :=
    NativeDenseSchemeFunctionField.exists_dense_affine_chart_with_functionField ℂ B hC X hInt hft
  let := hV
  let Y := chartVariety B hC V hV hs hl hq
  let := PrimitiveNativeDenseChartPresentation.restrictedOpen_nonempty B hC X U f V j hj hInt hdj hf
  let := PrimitiveNativeDenseChartPresentation.mapToChart_isDominant B hC X U f V j hj hf
  exact PrimitiveGeometricQuotientRationalOpen.rationalOpen
    (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj) Y
    (PrimitiveNativeDenseChartPresentation.mapToChart B hC X U f V j hj)
    (restrictedGeometry B hC X U f V j hj hInt hdj hf h)
    (originalChart ℂ B hC X V j) hjo

/-- The original native rational-function carrier is rational over its
actual structural C map. Both comparisons use the SAME derived chart. -/
theorem nonempty_nativeRationalFieldEquiv
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC X.obj)
    (hft : Space.IsLocallyOfFiniteType B (Spec (.of ℂ)) hC
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of ℂ)) hC).from X.obj))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : ClassifierGeometry B hC X U f) :
    letI := Space.functionField B (Spec (.of ℂ)) hC X.property hInt
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC X.property hInt
    Nonempty (Space.rationalFunctions B (Spec (.of ℂ)) hC X.property ≃ₐ[ℂ]
      M9.RationalField ℂ 24) := by
  let := Space.functionField B (Spec (.of ℂ)) hC X.property hInt
  let := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC X.property hInt
  obtain ⟨V, j, hV, _, _, _, _, hj, hdj, _, hFF⟩ :=
    NativeDenseSchemeFunctionField.exists_dense_affine_chart_with_functionField ℂ B hC X hInt hft
  let : IsIntegral ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V) := hV
  let := PrimitiveNativeDenseChartPresentation.restrictedOpen_nonempty B hC X U f V j hj hInt hdj hf
  let := PrimitiveNativeDenseChartPresentation.mapToChart_isDominant B hC X U f V j hj hf
  let : Algebra ℂ ((BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V).functionField :=
    (GrassmannianCharts.structureScalarMap
      (X := (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V) ℂ (B.inclusion.map V.hom)).toAlgebra
  obtain ⟨e⟩ := hFF
  exact ⟨e.trans (PrimitiveGeometricQuotientField.rationalEquiv
    (Y := (BigFppfOver.toScheme B (Spec (.of ℂ)) hC).obj V)
    (PrimitiveNativeDenseChartPresentation.restrictedOpen B hC X U f V j hj)
    (B.inclusion.map V.hom) (PrimitiveNativeDenseChartPresentation.mapToChart B hC X U f V j hj)
    (restrictedGeometry B hC X U f V j hj hInt hdj hf h))⟩

/-- Select the actual native-field equivalence just derived from geometry. -/
def nativeRationalFieldEquiv
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC X.obj)
    (hft : Space.IsLocallyOfFiniteType B (Spec (.of ℂ)) hC
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of ℂ)) hC).from X.obj))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : ClassifierGeometry B hC X U f) :
    letI := Space.functionField B (Spec (.of ℂ)) hC X.property hInt
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC X.property hInt
    Space.rationalFunctions B (Spec (.of ℂ)) hC X.property ≃ₐ[ℂ]
      M9.RationalField ℂ 24 :=
  Classical.choice (nonempty_nativeRationalFieldEquiv B hC X U f hInt hft hf h)

/-- The original complex coefficient inclusion is retained. -/
theorem nativeRationalFieldEquiv_coefficient
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC X.obj)
    (hft : Space.IsLocallyOfFiniteType B (Spec (.of ℂ)) hC
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of ℂ)) hC).from X.obj))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : ClassifierGeometry B hC X U f) (c : ℂ) :
    letI := Space.functionField B (Spec (.of ℂ)) hC X.property hInt
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC X.property hInt
    nativeRationalFieldEquiv B hC X U f hInt hft hf h
        (AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseMap ℂ B hC X.property hInt c) =
      algebraMap ℂ (M9.RationalField ℂ 24) c := by
  let := Space.functionField B (Spec (.of ℂ)) hC X.property hInt
  let := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC X.property hInt
  exact (nativeRationalFieldEquiv B hC X U f hInt hft hf h).commutes c

/-- The inverse retains the same actual structural coefficient inclusion. -/
theorem nativeRationalFieldEquiv_inverse_coefficient
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC X.obj)
    (hft : Space.IsLocallyOfFiniteType B (Spec (.of ℂ)) hC
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of ℂ)) hC).from X.obj))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : ClassifierGeometry B hC X U f) (c : ℂ) :
    letI := Space.functionField B (Spec (.of ℂ)) hC X.property hInt
    letI := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC X.property hInt
    (nativeRationalFieldEquiv B hC X U f hInt hft hf h).symm
        (algebraMap ℂ (M9.RationalField ℂ 24) c) =
      AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseMap ℂ B hC X.property hInt c := by
  let := Space.functionField B (Spec (.of ℂ)) hC X.property hInt
  let := AlgebraicSpaceFunctionFieldScalars.rationalFunctionsBaseAlgebra ℂ B hC X.property hInt
  exact (nativeRationalFieldEquiv B hC X U f hInt hft hf h).symm.commutes c

end M9Native.PrimitiveNativeClassifierRationalOpen

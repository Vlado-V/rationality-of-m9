module

public import M9StacksIntegration.GenusNineCoverParameterSchemes
public import M9StacksIntegration.FixedDegreeCoverCurveGraphAdapter
public import M9StacksIntegration.BoundedCoverFamily

/-! Genuine bounded-cover families from the actual five representing
schemes of each constructed original affine polarized genus-nine model.
The graph HP and degree cover data are derived from the representing map;
no graph membership, line comparison, or numerical degree is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.GenusNineBoundedCoverFamilies

open GenusNineCoverParameterSchemes

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K))) {m : ℕ}
  (D : GenusNineGroundFieldPolarizedModels.Model.{u} K m)

abbrev sourceAlgebraic := (schemeSpace (sourceSite K B hK D)).property
abbrev targetAlgebraic := (schemeSpace (targetSite K B hK D)).property
abbrev baseAlgebraic := (schemeSpace (baseSite K B hK D)).property
abbrev sourceProper := PolarizedCurveCoverScheme.sourceProper B (sourceContained K B hK D)
  (parameterContained K B hK D) D.projection
abbrev sourceFlat := PolarizedCurveCoverScheme.sourceFlat B (sourceContained K B hK D)
  (parameterContained K B hK D) D.projection
abbrev sourceFinitePresentation := PolarizedCurveCoverScheme.sourceFinitePresentation B
  (sourceContained K B hK D) (parameterContained K B hK D) D.projection
abbrev targetSeparated := PolarizedCurveCoverScheme.targetSeparated B (targetContained K B hK D)
  (parameterContained K B hK D) (targetProjection K D)
abbrev targetFinitePresentation := PolarizedCurveCoverScheme.targetFinitePresentation B
  (targetContained K B hK D) (parameterContained K B hK D) (targetProjection K D)
abbrev sourceNativeLine := PolarizedCurveCoverScheme.sourceLine B (sourceContained K B hK D) D.line
abbrev targetNativeLine := PolarizedCurveCoverScheme.targetLine B (targetContained K B hK D) (targetLine K D)

instance originalBaseAffine : IsAffine
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj (baseSite K B hK D)) := by
  change IsAffine D.parameter
  infer_instance

instance originalSourceProper : IsProper
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (sourceMap K B hK D)) := by
  change IsProper D.projection
  infer_instance

instance originalSourceSmooth : SmoothOfRelativeDimension 1
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (sourceMap K B hK D)) := by
  change SmoothOfRelativeDimension 1 D.projection
  infer_instance

/-- Actual data of a genuine representing scheme, produced below by
`exists_presentations`. The universal curve is not additional data. -/
structure Presentation (i : Fin 5) where
  parameter : BigFppfOver B integerBase (B.contains_integerBase)
  representative : yoneda.obj parameter ⟶
    (locus K B hK D (BoundedPencilGraphPolynomial.degreeIndex i)).toFunctor
  parameterMap : parameter ⟶ baseSite K B hK D
  representing : IsIso representative
  projection_triangle : representative ≫
    GenusNineCoverParameterSchemes.projection K B hK D
      (BoundedPencilGraphPolynomial.degreeIndex i) = yoneda.map parameterMap
  finiteType : Space.QuasiCompactFiniteType
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map parameterMap)

attribute [instance] Presentation.representing

/-- The five actual presentations exist by the original native affine
Hom theorem with the constructed source and true projective-line target. -/
theorem exists_presentations : Nonempty (∀ i : Fin 5, Presentation K B hK D i) := by
  obtain ⟨Y,A,q,hA,hq,hft⟩ := exists_five_parameterSchemes K B hK D
  exact ⟨fun i => ⟨Y i,A i,q i,hA i,hq i,hft i⟩⟩

namespace Presentation

variable {K B hK D} {i : Fin 5} (P : Presentation K B hK D i)

/-- The actual universal relative morphism of this actual Hilbert locus. -/
abbrev nativeFamily := FixedDegreeCoverScheme.universalRelativeMorphism (baseSite K B hK D)
  (sourceAlgebraic K B hK D) (targetAlgebraic K B hK D) (baseAlgebraic K B hK D)
  (targetSeparated K B hK D) (targetFinitePresentation K B hK D)
  (sourceFinitePresentation K B hK D) (sourceFlat K B hK D) (sourceProper K B hK D)
  (sourceNativeLine K B hK D) (targetNativeLine K B hK D)
  (BoundedPencilGraphPolynomial.degreeIndex i) P.representative

abbrev sourceRepresentable :=
  Functor.relativelyRepresentable.map yoneda (sourceMap K B hK D)

abbrev totalSite := RelativeCoverSchemeEvaluation.source (sourceMap K B hK D) (targetMap K B hK D)
  P.nativeFamily (sourceRepresentable (K := K) (B := B) (hK := hK) (D := D))

abbrev totalProjection := (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
  (RelativeCoverSchemeEvaluation.projection (sourceMap K B hK D) (targetMap K B hK D)
    P.nativeFamily (sourceRepresentable (K := K) (B := B) (hK := hK) (D := D)))

abbrev groundMap := FixedDegreeCoverCurveGraphAdapter.originalGroundMap (sourceMap K B hK D)
  (targetMap K B hK D) P.nativeFamily K D.structureMap

abbrev lineMap := FixedDegreeCoverCurveGraphAdapter.originalLineMap (sourceMap K B hK D)
  (targetMap K B hK D) P.nativeFamily (sourceRepresentable (K := K) (B := B) (hK := hK) (D := D)) K
  (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap)

/-- The native base triangle is derived from the actual representing map. -/
theorem nativeBase_eq : P.nativeFamily.base = yoneda.map P.parameterMap :=
  FixedDegreeCoverScheme.universalRelativeMorphism_base (baseSite K B hK D)
    (sourceAlgebraic K B hK D) (targetAlgebraic K B hK D) (baseAlgebraic K B hK D)
    (targetSeparated K B hK D) (targetFinitePresentation K B hK D)
    (sourceFinitePresentation K B hK D) (sourceFlat K B hK D) (sourceProper K B hK D)
    (sourceNativeLine K B hK D) (targetNativeLine K B hK D)
    (BoundedPencilGraphPolynomial.degreeIndex i) P.representative P.parameterMap P.projection_triangle

/-- The original ground map uses the SAME actual finite-type parameter map. -/
theorem groundMap_eq : P.groundMap =
    (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map P.parameterMap ≫ D.structureMap := by
  simp only [groundMap, FixedDegreeCoverCurveGraphAdapter.originalGroundMap,
    RelativeCoverSchemeEvaluation.base, P.nativeBase_eq, Functor.preimage_map]

/-- This original family has the full all-original-field scheme-curve
condition, through the actual original source square. -/
theorem schemeCurve : M9StandaloneDraft.SchemeCurve P.totalProjection 9 :=
  M9StacksIntegration.StandaloneCurveCohomology.schemeCurve_of_isPullback D.projection
    P.totalProjection
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
      (RelativeCoverSchemeEvaluation.toOriginal (sourceMap K B hK D) (targetMap K B hK D)
        P.nativeFamily (sourceRepresentable (K := K) (B := B) (hK := hK) (D := D))))
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
      (RelativeCoverSchemeEvaluation.base (sourceMap K B hK D) (targetMap K B hK D) P.nativeFamily))
    (RelativeCoverSchemeEvaluation.originalSourceSquare (sourceMap K B hK D) (targetMap K B hK D)
      P.nativeFamily (sourceRepresentable (K := K) (B := B) (hK := hK) (D := D))) D.schemeCurve

/-- The parameter's actual structural finiteness is derived from its
representing scheme and the genuine finite-type affine source base. -/
theorem parameterGeometry : LocallyOfFiniteType P.groundMap ∧ QuasiCompact P.groundMap ∧
    IsNoetherian ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj P.parameter) := by
  letI := P.finiteType.1
  letI := P.finiteType.2
  have hft : LocallyOfFiniteType P.groundMap := by rw [P.groundMap_eq]; infer_instance
  have hqc : QuasiCompact P.groundMap := by rw [P.groundMap_eq]; infer_instance
  letI := hft
  letI := hqc
  letI : IsLocallyNoetherian
      ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj P.parameter) :=
    LocallyOfFiniteType.isLocallyNoetherian P.groundMap
  letI : CompactSpace
      ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj P.parameter) :=
    QuasiCompact.compactSpace_of_compactSpace P.groundMap
  exact ⟨hft,hqc,⟨⟩⟩

/-- The actual universal Hilbert locus supplies a genuine nonconstant
cover of degree one through five on every native-contained field fibre. -/
def boundedFamily : BoundedCoverFamily B K := by
  have hsource : FixedDegreeCoverCurveGraphAdapter.sourceGeometry (sourceMap K B hK D) D.line := by
    intro L _ V a q f _ sq
    exact D.fieldGeometry L V a q f sq
  have htarget : ConstantProjectiveLinePolarization.toGroundLine K D.structureMap ≫
      PencilProjectiveLineGeometry.toBase K =
        (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (targetMap K B hK D) ≫
          D.structureMap := ConstantProjectiveLinePolarization.originalSquare K D.structureMap |>.w
  have hc := FixedDegreeCoverCurveGraphAdapter.universal_hcover (sourceMap K B hK D)
    (targetMap K B hK D) (sourceRepresentable (K := K) (B := B) (hK := hK) (D := D)) D.line
    (targetSeparated K B hK D) (targetFinitePresentation K B hK D)
    (sourceFinitePresentation K B hK D) (sourceFlat K B hK D) (sourceProper K B hK D)
    K D.structureMap (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap) htarget
    hsource (BoundedPencilGraphPolynomial.degreeIndex i)
    (by have h := BoundedPencilGraphPolynomial.degreeIndex_bounds i; omega)
    (BoundedPencilGraphPolynomial.degreeIndex_bounds i).2 P.representative
  exact
    { parameter := (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj P.parameter
      total := (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj P.totalSite
      parameterContained := P.parameter.left.property
      totalContained := P.totalSite.left.property
      projection := P.totalProjection
      schemeCurve := P.schemeCurve
      structureMap := P.groundMap
      finiteType := P.parameterGeometry.1
      noetherian := P.parameterGeometry.2.2
      lineMap := P.lineMap
      lineMap_over := FixedDegreeCoverCurveGraphAdapter.originalLineMap_over
        (sourceMap K B hK D) (targetMap K B hK D) P.nativeFamily (sourceRepresentable (K := K) (B := B) (hK := hK) (D := D))
        K D.structureMap (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap) htarget
      fieldCover := hc }

end Presentation

end M9Native.GenusNineBoundedCoverFamilies
end

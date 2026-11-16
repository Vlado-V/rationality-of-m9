module

public import M9StacksIntegration.GenusNineFiniteEquationFamilies
public import M9StacksIntegration.GenusNinePolarizedSourceOpen
public import M9StacksIntegration.StandaloneCurveCohomology

/-! Finitely many actual polarized smooth genus-nine families.

The families are the genuine nested opens of the frozen finite equation
models. Their geometry is constructed by the actual smooth-genus-nine
and degree-forty-eight open, rather than supplied as an input. Their
original coefficient maps and projective ambient maps are retained.
Every original algebraically closed field is allowed in the coverage
theorem; there is no big-site cutoff.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
universe u
namespace M9Native.GenusNineBoundedPolarizedModels
open GenusNineFiniteEquationFamilies

abbrev coefficientToInteger (m : ℕ) :
    Spec (.of (coefficientRing.{u} m)) ⟶ Spec (.of (ULift.{u} ℤ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (coefficientRing.{u} m)))

/-- A native family with its literal projective polarization and all
derived geometry. This structure is an output of `exists_finite_models`. -/
structure Family (m : ℕ) where
  parameter : Scheme.{u}
  total : Scheme.{u}
  projection : total ⟶ parameter
  line : total.Modules
  isInvertible : SheafOfModules.IsInvertible total.presheaf total.ringCatSheaf.2 line
  isProper : IsProper projection
  flat : Flat projection
  smoothRelativeDimension : SmoothOfRelativeDimension 1 projection
  coefficientMap : parameter ⟶ Spec (.of (coefficientRing.{u} m))
  parameterNoetherian : IsNoetherian parameter
  parameterFinitePresentation : LocallyOfFinitePresentation
    (coefficientMap ≫ coefficientToInteger.{u} m)
  parameterQuasiCompact : QuasiCompact (coefficientMap ≫ coefficientToInteger.{u} m)
  relativelyAmple : letI := isInvertible
    Stacks.RelativeAmple.IsRelativelyAmple projection line
  ambientMap : total ⟶ projectiveSpaceOverRing 39 (.of (coefficientRing.{u} m))
  ambient_overBase : ambientMap ≫
      (projectiveSpaceOverRing 39 (.of (coefficientRing.{u} m)) ↘
        Spec (.of (coefficientRing.{u} m))) = projection ≫ coefficientMap
  lineIso : line ≅ (Scheme.Modules.pullback ambientMap).obj
    (twistOver 39 (Spec (.of (coefficientRing.{u} m))) 1)
  fieldGeometry : ∀ (K : Type u) [Field K] (V : Scheme.{u})
    (y : Spec (.of K) ⟶ parameter) (q : V ⟶ total) (f : V ⟶ Spec (.of K))
    [IsProper f], IsPullback q f projection y →
      IsCurve K f ∧ IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) ∧ genus f = 9 ∧
        ∀ hdim : topologicalKrullDim V ≤ 1,
          invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj line) = 48

attribute [instance] Family.isInvertible Family.isProper Family.flat
  Family.smoothRelativeDimension Family.parameterNoetherian

instance Family.isSmooth {m : ℕ} (D : Family.{u} m) : Smooth D.projection :=
  SmoothOfRelativeDimension.smooth 1 D.projection

/-- Constants on every original field square give genuine geometric
connectedness of the entire actual family. -/
theorem Family.geometricallyConnected {m : ℕ} (D : Family.{u} m) :
    GeometricallyConnected D.projection := by
  refine ⟨?_⟩
  intro L _ a V q f sq
  letI : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) sq D.isProper
  have hH0 := (D.fieldGeometry L V a q f sq).2.1
  exact @connectedSpace_of_isIso_globalSections L _ V f hH0

/-- The original scheme-curve predicate, including finite H1 of genus
nine on every original field-valued point, is derived from the actual
finite-family geometry. No native membership hypothesis is supplied. -/
theorem Family.schemeCurve {m : ℕ} (D : Family.{u} m) :
    M9StandaloneDraft.SchemeCurve D.projection 9 := by
  refine ⟨D.isProper, D.smoothRelativeDimension, D.geometricallyConnected, ?_⟩
  intro L _ a
  letI : IsProper (pullback.snd D.projection a) := inferInstance
  have h := D.fieldGeometry L (pullback D.projection a) a
    (pullback.fst D.projection a) (pullback.snd D.projection a)
    (IsPullback.of_hasPullback D.projection a)
  refine ⟨M9StacksIntegration.StandaloneCurveCohomology.finite_standalone_H1
    (pullback.snd D.projection a), ?_⟩
  change genus (pullback.snd D.projection a) = 9
  exact h.2.2.1

abbrev modelProjection (m : ℕ) {T : Scheme.{u}}
    (j : T ⟶ Spec (.of (coefficientRing.{u} m))) :=
  pullback.snd (universalProjection.{u} m) j

abbrev originalLine (m : ℕ) {T : Scheme.{u}}
    (j : T ⟶ Spec (.of (coefficientRing.{u} m))) :=
  GenusNineFiniteEquationFamilies.modelLine.{u} m j

section OriginalModel
variable (m : ℕ) {T : Scheme.{u}}
  (j : T ⟶ Spec (.of (coefficientRing.{u} m)))
variable [IsProper (modelProjection m j)] [Flat (modelProjection m j)] [LocallyOfFinitePresentation (modelProjection m j)]

local instance originalLineInvertible :
    SheafOfModules.IsInvertible (pullback (universalProjection.{u} m) j).presheaf
      (pullback (universalProjection.{u} m) j).ringCatSheaf.2 (originalLine m j) :=
  FiniteEquationEmbedding.modelLine_isInvertible 39 (equationCount m) m j

abbrev parameter (U : T.Opens) : Scheme.{u} :=
  (GenusNinePolarizedSourceOpen.boundedOpen (modelProjection m j) (originalLine m j) U).toScheme

abbrev total (U : T.Opens) : Scheme.{u} :=
  (((modelProjection m j) ∣_ U) ⁻¹ᵁ GenusNinePolarizedSourceOpen.boundedOpen (modelProjection m j) (originalLine m j) U).toScheme

abbrev coefficientMap (U : T.Opens) :
    parameter m j U ⟶ Spec (.of (coefficientRing.{u} m)) :=
  GenusNinePolarizedSourceOpen.baseMap (modelProjection m j) (originalLine m j) U ≫ j

abbrev ambientMap (U : T.Opens) :
    total m j U ⟶ projectiveSpaceOverRing 39 (.of (coefficientRing.{u} m)) :=
  GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U ≫
    pullback.fst (universalProjection.{u} m) j ≫ universalEmbedding.{u} m

/-- The two actual open restrictions retain the original model line. -/
def lineOriginalIso (U : T.Opens) :
    GenusNinePolarizedSourceOpen.line (modelProjection m j) (originalLine m j) U ≅
      (Scheme.Modules.pullback (GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U)).obj (originalLine m j) :=
  (Scheme.Modules.pullbackComp
    (((modelProjection m j) ∣_ U) ⁻¹ᵁ GenusNinePolarizedSourceOpen.boundedOpen (modelProjection m j) (originalLine m j) U).ι
    ((modelProjection m j) ⁻¹ᵁ U).ι).app (originalLine m j)

theorem line_isInvertible (U : T.Opens) :
    SheafOfModules.IsInvertible (total m j U).presheaf
      (total m j U).ringCatSheaf.2 (GenusNinePolarizedSourceOpen.line (modelProjection m j) (originalLine m j) U) := by
  dsimp only [GenusNinePolarizedSourceOpen.line, GenusNinePolarizedSourceOpen.firstLine]
  infer_instance

/-- The final family's line is the pullback of its actual ambient O(1). -/
def lineAmbientIso (U : T.Opens) :
    GenusNinePolarizedSourceOpen.line (modelProjection m j) (originalLine m j) U ≅
      (Scheme.Modules.pullback (ambientMap m j U)).obj
        (twistOver 39 (Spec (.of (coefficientRing.{u} m))) 1) :=
  lineOriginalIso m j U ≪≫
    (Scheme.Modules.pullback (GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U)).mapIso
      ((Scheme.Modules.pullbackComp (pullback.fst (universalProjection.{u} m) j)
        (universalEmbedding.{u} m)).app _) ≪≫
    (Scheme.Modules.pullbackComp (GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U)
      (pullback.fst (universalProjection.{u} m) j ≫ universalEmbedding.{u} m)).app _

theorem ambientMap_overBase (U : T.Opens) :
    ambientMap m j U ≫
      (projectiveSpaceOverRing 39 (.of (coefficientRing.{u} m)) ↘
        Spec (.of (coefficientRing.{u} m))) =
      GenusNinePolarizedSourceOpen.projection (modelProjection m j) (originalLine m j) U ≫ coefficientMap m j U := by
  have hu : universalEmbedding.{u} m ≫
        (projectiveSpaceOverRing 39 (.of (coefficientRing.{u} m)) ↘
          Spec (.of (coefficientRing.{u} m))) = universalProjection.{u} m :=
    FiniteEquationEmbedding.formsEmbedding_toSpec (coefficientRing.{u} m)
      (Stacks.UniversalForms.form 39 (equationCount m) m)
      (Stacks.UniversalForms.isHomogeneous_form 39 (equationCount m) m)
  calc
    _ = GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U ≫
        pullback.fst (universalProjection.{u} m) j ≫ universalProjection.{u} m := by
      simp only [ambientMap, Category.assoc, hu]
    _ = GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U ≫ (modelProjection m j) ≫ j := by
      rw [pullback.condition]
    _ = (GenusNinePolarizedSourceOpen.projection (modelProjection m j) (originalLine m j) U ≫
        GenusNinePolarizedSourceOpen.baseMap (modelProjection m j) (originalLine m j) U) ≫ j := by
      have hs := (GenusNinePolarizedSourceOpen.originalSquare
        (modelProjection m j) (originalLine m j) U).w
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun a : total m j U ⟶ T => a ≫ j) hs)
    _ = _ := Category.assoc _ _ _

/-- Actual original parameter finiteness over the integer base is
inherited by the two genuine opens of a Noetherian equation stratum. -/
theorem parameter_geometry [IsImmersion j] [IsNoetherian T] (U : T.Opens) :
    IsNoetherian (parameter m j U) ∧
      LocallyOfFinitePresentation (coefficientMap m j U ≫ coefficientToInteger.{u} m) ∧
      QuasiCompact (coefficientMap m j U ≫ coefficientToInteger.{u} m) := by
  letI : IsLocallyNoetherian U.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian U.ι
  letI : IsLocallyNoetherian (parameter m j U) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (GenusNinePolarizedSourceOpen.boundedOpen (modelProjection m j) (originalLine m j) U).ι
  letI : CompactSpace (parameter m j U) := inferInstance
  letI : IsNoetherian (parameter m j U) := ⟨⟩
  have hp := EquationParameterGeometry.projection_geometry
    (ULift.{u} ℤ) (coefficientRing.{u} m) j
  letI := hp.1
  have hft := GenusNinePolarizedSourceOpen.baseMap_finiteType (modelProjection m j) (originalLine m j)
    (EquationParameterGeometry.projection (ULift.{u} ℤ) (coefficientRing.{u} m) j) U
  refine ⟨inferInstance, ?_, ?_⟩
  · have h : LocallyOfFinitePresentation
        (GenusNinePolarizedSourceOpen.baseMap (modelProjection m j) (originalLine m j) U ≫
          EquationParameterGeometry.projection (ULift.{u} ℤ) (coefficientRing.{u} m) j) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hft.1
    simpa only [coefficientMap, coefficientToInteger,
      EquationParameterGeometry.projection, Category.assoc] using h
  · simpa only [coefficientMap, coefficientToInteger,
      EquationParameterGeometry.projection, Category.assoc] using hft.2

/-- The actual lifted curve retains its original model polarization. -/
def liftedLineIso (U : T.Opens) {V : Scheme.{u}}
    (q' : V ⟶ total m j U) (q : V ⟶ pullback (universalProjection.{u} m) j)
    (hq : q' ≫ GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U = q) :
    (Scheme.Modules.pullback q').obj (GenusNinePolarizedSourceOpen.line (modelProjection m j) (originalLine m j) U) ≅
      (Scheme.Modules.pullback q).obj (originalLine m j) :=
  (Scheme.Modules.pullback q').mapIso (lineOriginalIso m j U) ≪≫
    (Scheme.Modules.pullbackComp q' (GenusNinePolarizedSourceOpen.totalMap (modelProjection m j) (originalLine m j) U)).app (originalLine m j) ≪≫
    (Scheme.Modules.pullbackCongr hq).app (originalLine m j)
end OriginalModel

/-- Finitely many actual smooth proper genus-nine polarized families
cover every original algebraically closed curve, preserving the native
tricanonical embedding and its literal projective ambient triangle. -/
theorem exists_finite_models :
    ∃ (m t : ℕ) (D : Fin t → Family.{u} m),
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (V : Scheme.{u})
        (f : V ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
        [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (_ : genus f = 9),
        ∃ i, ∃ (y : Spec (.of K) ⟶ (D i).parameter) (q : V ⟶ (D i).total)
          (κ : V ⟶ projectiveSpaceOverRing 39 (.of K)),
          IsPullback q f (D i).projection y ∧ IsClosedImmersion κ ∧
          κ ≫ (projectiveSpaceOverRing 39 (.of K) ↘ Spec (.of K)) = f ∧
          q ≫ (D i).ambientMap =
            κ ≫ projectiveSpaceOverMap 39 (y ≫ (D i).coefficientMap) ∧
          Nonempty ((Scheme.Modules.pullback κ).obj (twistOver 39 (Spec (.of K)) 1) ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          Nonempty ((Scheme.Modules.pullback q).obj (D i).line ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          ∀ hdim : topologicalKrullDim V ≤ 1,
            invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj (D i).line) = 48 := by
  classical
  obtain ⟨m, t, T, j, hj, hT, _hfp, _hqc, hflat, hproper, hcover⟩ :=
    GenusNineFiniteEquationFamilies.exists_finite_curve_models_embedded.{u}
  let p := fun i : Fin t => pullback.snd (universalProjection.{u} m) (j i)
  let N := fun i : Fin t => GenusNineFiniteEquationFamilies.modelLine.{u} m (j i)
  letI (i : Fin t) : IsNoetherian (T i) := hT i
  letI (i : Fin t) : IsImmersion (j i) := hj i
  letI (i : Fin t) : IsProper (p i) := hproper i
  letI (i : Fin t) : Flat (p i) := hflat i
  letI (i : Fin t) : LocallyOfFinitePresentation (p i) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
      (hproper i).toLocallyOfFiniteType
  letI (i : Fin t) : SheafOfModules.IsInvertible
      (pullback (universalProjection.{u} m) (j i)).presheaf
      (pullback (universalProjection.{u} m) (j i)).ringCatSheaf.2 (N i) :=
    FiniteEquationEmbedding.modelLine_isInvertible 39 (equationCount m) m (j i)
  choose U hsm hgeom hlift using fun i : Fin t =>
    GenusNinePolarizedSourceOpen.exists_polarizedSourceOpen (p i) (N i)
  let D : Fin t → Family.{u} m := fun i =>
    { parameter := parameter m (j i) (U i)
      total := total m (j i) (U i)
      projection := GenusNinePolarizedSourceOpen.projection (p i) (N i) (U i)
      line := GenusNinePolarizedSourceOpen.line (p i) (N i) (U i)
      isInvertible := line_isInvertible m (j i) (U i)
      isProper := inferInstance
      flat := inferInstance
      smoothRelativeDimension := hsm i
      coefficientMap := coefficientMap m (j i) (U i)
      parameterNoetherian := (parameter_geometry m (j i) (U i)).1
      parameterFinitePresentation := (parameter_geometry m (j i) (U i)).2.1
      parameterQuasiCompact := (parameter_geometry m (j i) (U i)).2.2
      relativelyAmple := GenusNinePolarizedSourceOpen.line_isRelativelyAmple
        (p i) (N i) (U i)
        (FiniteEquationEmbedding.modelLine_isRelativelyAmple 39 (equationCount m) m (j i))
      ambientMap := ambientMap m (j i) (U i)
      ambient_overBase := ambientMap_overBase m (j i) (U i)
      lineIso := lineAmbientIso m (j i) (U i)
      fieldGeometry := hgeom i }
  refine ⟨m, t, D, ?_⟩
  intro K _ _ V f _ _ _ _ hg
  obtain ⟨i, y, q, κ, sq, hκ, hκbase, htriangle, ⟨eκ⟩, ⟨eN⟩, hdegree⟩ :=
    hcover K V f hg
  obtain ⟨y', q', hy', hq', sq'⟩ := hlift i K V y q f hg
    (hdegree (IsCurve.topologicalKrullDim_eq_one (f := f)).le) sq
  let eLine := liftedLineIso m (j i) (U i) q' q hq' ≪≫ eN
  refine ⟨i, y', q', κ, sq', hκ, hκbase, ?_, ⟨eκ⟩, ⟨eLine⟩, ?_⟩
  · have hc : y' ≫ coefficientMap m (j i) (U i) = y ≫ j i := by
      rw [coefficientMap, ← Category.assoc, hy']
    change q' ≫ ambientMap m (j i) (U i) =
      κ ≫ projectiveSpaceOverMap 39 (y' ≫ coefficientMap m (j i) (U i))
    rw [ambientMap, ← Category.assoc q' (GenusNinePolarizedSourceOpen.totalMap (p i) (N i) (U i)),
      hq', hc]
    exact htriangle
  · intro hdim
    exact (invertibleCurveDegree_eq_of_iso K f hdim eLine).trans
      (GenusNineTricanonicalCohomology.tricanonical_degree f hdim hg)

/-- Every open of the actual Noetherian parameter is Noetherian. -/
theorem Family.open_isNoetherian {m : ℕ} (D : Family.{u} m) (U : D.parameter.Opens) :
    IsNoetherian U.toScheme := by
  letI : IsLocallyNoetherian U.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian U.ι
  letI : CompactSpace U.toScheme := inferInstance
  exact ⟨⟩

/-- Restrict an actual constructed family along an actual parameter
open, keeping its original coefficient and projective ambient maps. -/
def Family.restrict {m : ℕ} (D : Family.{u} m) (U : D.parameter.Opens) : Family.{u} m := by
  letI := D.open_isNoetherian U
  letI := D.parameterFinitePresentation
  letI := D.parameterQuasiCompact
  refine
    { parameter := U.toScheme
      total := (D.projection ⁻¹ᵁ U).toScheme
      projection := D.projection ∣_ U
      line := (Scheme.Modules.pullback (D.projection ⁻¹ᵁ U).ι).obj D.line
      isInvertible := Stacks.InvertiblePullback.isInvertibleModule_pullback
        (D.projection ⁻¹ᵁ U).ι D.line
      isProper := inferInstance
      flat := inferInstance
      smoothRelativeDimension :=
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
          (isPullback_morphismRestrict D.projection U).flip D.smoothRelativeDimension
      coefficientMap := U.ι ≫ D.coefficientMap
      parameterNoetherian := inferInstance
      parameterFinitePresentation := ?_
      parameterQuasiCompact := ?_
      relativelyAmple :=
        Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_morphismRestrict
          D.projection D.line D.relativelyAmple U
      ambientMap := (D.projection ⁻¹ᵁ U).ι ≫ D.ambientMap
      ambient_overBase := ?_
      lineIso := (Scheme.Modules.pullback (D.projection ⁻¹ᵁ U).ι).mapIso D.lineIso ≪≫
        (Scheme.Modules.pullbackComp (D.projection ⁻¹ᵁ U).ι D.ambientMap).app _
      fieldGeometry := ?_ }
  · have h : LocallyOfFinitePresentation
        (U.ι ≫ (D.coefficientMap ≫ coefficientToInteger.{u} m)) := inferInstance
    simpa only [Category.assoc] using h
  · have h : QuasiCompact
        (U.ι ≫ (D.coefficientMap ≫ coefficientToInteger.{u} m)) := inferInstance
    simpa only [Category.assoc] using h
  · have hs := morphismRestrict_ι D.projection U
    calc
      _ = (D.projection ⁻¹ᵁ U).ι ≫
          (D.ambientMap ≫ (projectiveSpaceOverRing 39 (.of (coefficientRing.{u} m)) ↘
            Spec (.of (coefficientRing.{u} m)))) := Category.assoc _ _ _
      _ = (D.projection ⁻¹ᵁ U).ι ≫ (D.projection ≫ D.coefficientMap) :=
        congrArg (fun a => (D.projection ⁻¹ᵁ U).ι ≫ a) D.ambient_overBase
      _ = ((D.projection ∣_ U) ≫ U.ι) ≫ D.coefficientMap :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun a : (D.projection ⁻¹ᵁ U).toScheme ⟶ D.parameter =>
            a ≫ D.coefficientMap) hs.symm)
      _ = _ := Category.assoc _ _ _
  · intro K _ V y q f _ sq
    have hbig := sq.paste_horiz (isPullback_morphismRestrict D.projection U).flip
    have h := D.fieldGeometry K V (y ≫ U.ι) (q ≫ (D.projection ⁻¹ᵁ U).ι) f hbig
    letI := Stacks.InvertiblePullback.isInvertibleModule_pullback
      (D.projection ⁻¹ᵁ U).ι D.line
    letI : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        ((Scheme.Modules.pullback (D.projection ⁻¹ᵁ U).ι ⋙
          Scheme.Modules.pullback q).obj D.line) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback q
        ((Scheme.Modules.pullback (D.projection ⁻¹ᵁ U).ι).obj D.line)
    refine ⟨h.1, h.2.1, h.2.2.1, fun hd => ?_⟩
    exact (invertibleCurveDegree_eq_of_iso K f hd
      ((Scheme.Modules.pullbackComp q (D.projection ⁻¹ᵁ U).ι).app D.line)).trans
        (h.2.2.2 hd)

/-- A lifted original curve keeps the same literal family line after
restriction to a parameter open. -/
def Family.restrictPullbackIso {m : ℕ} (D : Family.{u} m) (U : D.parameter.Opens)
    {V : Scheme.{u}} (q' : V ⟶ (D.restrict U).total) (q : V ⟶ D.total)
    (hq : q' ≫ (D.projection ⁻¹ᵁ U).ι = q) :
    (Scheme.Modules.pullback q').obj (D.restrict U).line ≅
      (Scheme.Modules.pullback q).obj D.line :=
  (Scheme.Modules.pullbackComp q' (D.projection ⁻¹ᵁ U).ι).app D.line ≪≫
    (Scheme.Modules.pullbackCongr hq).app D.line

/-- The actual quasi-compact parameter has finitely many actual affine
open subsets covering every one of its points. -/
theorem Family.exists_finite_affine_opens {m : ℕ} (D : Family.{u} m) :
    ∃ (n : ℕ) (U : Fin n → D.parameter.Opens),
      (∀ a, IsAffineOpen (U a)) ∧ ∀ z : D.parameter, ∃ a, z ∈ U a := by
  classical
  let c := D.parameter.affineCover.finiteSubcover
  let e := Fintype.equivFin c.I₀
  refine ⟨Fintype.card c.I₀, fun a => (c.f (e.symm a)).opensRange, ?_, ?_⟩
  · intro a
    letI : IsAffine (c.X (e.symm a)) := inferInstance
    exact isAffineOpen_opensRange (c.f (e.symm a))
  · intro z
    refine ⟨e (c.idx z), ?_⟩
    have hmem : z ∈ (c.f (c.idx z)).opensRange := c.covers z
    exact (congrArg (fun a : c.I₀ => z ∈ (c.f a).opensRange)
      (e.symm_apply_apply (c.idx z))).mpr hmem

/-- Finitely many actual AFFINE parameter families suffice for the
original fixed-polynomial cover construction. The finite index is a
literal finite sum of finite sets. Every original ACL curve still lifts
with its actual tricanonical map, ambient triangle and line isomorphism. -/
theorem exists_finite_affine_models :
    ∃ (m t : ℕ) (n : Fin t → ℕ)
      (D : (Σ i : Fin t, Fin (n i)) → Family.{u} m),
      (∀ a, IsAffine (D a).parameter) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (V : Scheme.{u})
        (f : V ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
        [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (_ : genus f = 9),
        ∃ a, ∃ (y : Spec (.of K) ⟶ (D a).parameter) (q : V ⟶ (D a).total)
          (κ : V ⟶ projectiveSpaceOverRing 39 (.of K)),
          IsPullback q f (D a).projection y ∧ IsClosedImmersion κ ∧
          κ ≫ (projectiveSpaceOverRing 39 (.of K) ↘ Spec (.of K)) = f ∧
          q ≫ (D a).ambientMap =
            κ ≫ projectiveSpaceOverMap 39 (y ≫ (D a).coefficientMap) ∧
          Nonempty ((Scheme.Modules.pullback κ).obj (twistOver 39 (Spec (.of K)) 1) ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          Nonempty ((Scheme.Modules.pullback q).obj (D a).line ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          ∀ hdim : topologicalKrullDim V ≤ 1,
            invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj (D a).line) = 48 := by
  classical
  obtain ⟨m,t,D,hcov⟩ := exists_finite_models.{u}
  choose n U hU hUc using fun i : Fin t => (D i).exists_finite_affine_opens
  let E := Σ i : Fin t, Fin (n i)
  let A : E → Family.{u} m := fun a => (D a.1).restrict (U a.1 a.2)
  refine ⟨m,t,n,A,?_,?_⟩
  · rintro ⟨i,a⟩
    exact hU i a
  · intro K _ _ V f _ _ _ _ hg
    obtain ⟨i,y,q,κ,sq,hκ,hbase,htriangle,⟨eκ⟩,⟨eN⟩,_⟩ := hcov K V f hg
    obtain ⟨a,ha⟩ := hUc i (y (IsLocalRing.closedPoint K))
    obtain ⟨y',q',hy',hq',sq'⟩ :=
      exists_isPullback_restrict_of_mem (D i).projection (U i a) sq ha
    let eLine := (D i).restrictPullbackIso (U i a) q' q hq' ≪≫ eN
    refine ⟨⟨i,a⟩,y',q',κ,sq',hκ,hbase,?_,⟨eκ⟩,⟨eLine⟩,?_⟩
    · have hc : y' ≫ ((U i a).ι ≫ (D i).coefficientMap) = y ≫ (D i).coefficientMap :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun b => b ≫ (D i).coefficientMap) hy')
      change q' ≫ ((D i).projection ⁻¹ᵁ U i a).ι ≫ (D i).ambientMap =
        κ ≫ projectiveSpaceOverMap 39 (y' ≫ ((U i a).ι ≫ (D i).coefficientMap))
      rw [← Category.assoc q' ((D i).projection ⁻¹ᵁ U i a).ι, hq', hc]
      exact htriangle
    · intro hd
      exact (invertibleCurveDegree_eq_of_iso K f hd eLine).trans
        (GenusNineTricanonicalCohomology.tricanonical_degree f hd hg)

end M9Native.GenusNineBoundedPolarizedModels
end

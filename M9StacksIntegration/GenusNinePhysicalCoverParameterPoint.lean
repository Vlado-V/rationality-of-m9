module

public import M9StacksIntegration.GenusNineCoverParameterSchemes
public import M9StacksIntegration.RelativeCoverOfOriginalSquare
public import M9StacksIntegration.FixedDegreeCoverCurveGraphAdapter

/-! An original physical cover gives a point of one of the SAME five
actual representing schemes of its original polarized model. The native
field source and its cover map are compared by genuine pullback squares. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space M9Native.PencilProjectiveLineGeometry
attribute [local instance] isCurve_projectiveSpaceOver_one

universe u

namespace M9Native.GenusNinePhysicalCoverParameterPoint

open GenusNineCoverParameterSchemes

/-- The honest original physical data. Every geometric property and every
comparison with the chosen native source is derived from `cartesian`. -/
structure PhysicalCover {K : Type u} [Field K] {m : ℕ}
    (D : GenusNineGroundFieldPolarizedModels.Model.{u} K m)
    (L : Type u) [Field L] (coefficient : Spec (.of L) ⟶ Spec (.of K)) where
  source : Scheme.{u}
  projection : source ⟶ Spec (.of L)
  modelPoint : Spec (.of L) ⟶ D.parameter
  toModel : source ⟶ D.total
  cartesian : IsPullback toModel projection D.projection modelPoint
  coefficient_triangle : modelPoint ≫ D.structureMap = coefficient
  lineMap : source ⟶ Line L
  lineMap_over : lineMap ≫ toBase L = projection
  nonconstant : ¬ ∃ y : Line L, ∀ c : source, lineMap.base c = y

namespace PhysicalCover

variable {K : Type u} [Field K] {m : ℕ}
  {D : GenusNineGroundFieldPolarizedModels.Model.{u} K m}
  {L : Type u} [Field L] {coefficient : Spec (.of L) ⟶ Spec (.of K)}
  (c : PhysicalCover D L coefficient)

instance proper : IsProper c.projection :=
  MorphismProperty.of_isPullback (P := @IsProper) c.cartesian inferInstance

instance smooth : Smooth c.projection := by
  have : SmoothOfRelativeDimension 1 c.projection :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      c.cartesian inferInstance
  exact SmoothOfRelativeDimension.smooth 1 c.projection

instance isCurve : IsCurve L c.projection :=
  (D.fieldGeometry L c.source c.modelPoint c.toModel c.projection c.cartesian).1

instance constants : IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ c.projection.appTop) :=
  (D.fieldGeometry L c.source c.modelPoint c.toModel c.projection c.cartesian).2.1

/-- This is the original native function-field degree of the physical map. -/
abbrev nativeDegree : ℕ :=
  PencilDegreePullback.curveMapDegree c.projection (toBase L)
    c.lineMap c.lineMap_over c.nonconstant

/-- The map to the original constant target is its actual projective lift. -/
def originalTargetMap : c.source ⟶ target K D :=
  pullback.lift (c.lineMap ≫ projectiveSpaceOverMap 1 coefficient)
    (c.projection ≫ c.modelPoint) (by
      calc
        (c.lineMap ≫ projectiveSpaceOverMap 1 coefficient) ≫ toBase K =
            c.lineMap ≫ (toBase L ≫ coefficient) := by
          have hp : projectiveSpaceOverMap 1 coefficient ≫ toBase K =
              toBase L ≫ coefficient := (isPullback_projectiveSpaceOverMap 1 coefficient).w
          rw [Category.assoc, hp]
        _ = c.projection ≫ coefficient := by
          rw [← Category.assoc, c.lineMap_over]
        _ = (c.projection ≫ c.modelPoint) ≫ D.structureMap := by
          rw [Category.assoc, c.coefficient_triangle])

theorem originalTargetMap_over :
    c.originalTargetMap ≫ targetProjection K D = c.projection ≫ c.modelPoint :=
  pullback.lift_snd _ _ _

theorem originalTargetMap_toLine :
    c.originalTargetMap ≫ ConstantProjectiveLinePolarization.toGroundLine K D.structureMap =
      c.lineMap ≫ projectiveSpaceOverMap 1 coefficient :=
  pullback.lift_fst _ _ _

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  (hL : B.Contains (Spec (.of L)))

local instance originalSourceProper : IsProper
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (sourceMap K B hK D)) := by
  change IsProper D.projection
  infer_instance

local instance originalSourceSmooth : SmoothOfRelativeDimension 1
    ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (sourceMap K B hK D)) := by
  change SmoothOfRelativeDimension 1 D.projection
  infer_instance

abbrev sourceContained : B.Contains c.source :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact c.projection hL

abbrev physicalSite := integerSiteObject B (B.contains_integerBase) (c.sourceContained B hL)
abbrev basePoint := integerSiteMap B (B.contains_integerBase) hL
  (parameterContained K B hK D) c.modelPoint
abbrev sourcePoint := integerSiteMap B (B.contains_integerBase) (c.sourceContained B hL)
  (GenusNineCoverParameterSchemes.sourceContained K B hK D) c.toModel
abbrev projectionPoint := integerSiteMap B (B.contains_integerBase) (c.sourceContained B hL)
  hL c.projection
abbrev targetPoint := integerSiteMap B (B.contains_integerBase) (c.sourceContained B hL)
  (targetContained K B hK D) c.originalTargetMap

theorem siteSquare :
    IsPullback (c.sourcePoint B hK hL) (c.projectionPoint B hL)
      (sourceMap K B hK D) (c.basePoint B hK hL) :=
  RelativeCoverOfOriginalSquare.integerSiteSquare B (B.contains_integerBase)
    (c.sourceContained B hL) (GenusNineCoverParameterSchemes.sourceContained K B hK D)
    (parameterContained K B hK D) hL c.toModel c.projection D.projection c.modelPoint c.cartesian

theorem targetPoint_over :
    c.targetPoint B hK hL ≫ targetMap K B hK D =
      c.projectionPoint B hL ≫ c.basePoint B hK hL := by
  change integerSiteMap B (B.contains_integerBase) _ _ c.originalTargetMap ≫
      integerSiteMap B (B.contains_integerBase) _ _ (targetProjection K D) =
    integerSiteMap B (B.contains_integerBase) _ _ c.projection ≫
      integerSiteMap B (B.contains_integerBase) _ _ c.modelPoint
  rw [integerSiteMap_comp, integerSiteMap_comp, c.originalTargetMap_over]

/-- The actual native relative morphism is constructed from the physical square. -/
def nativeFamily := RelativeCoverOfOriginalSquare.relativeMorphism
  (sourceMap K B hK D) (targetMap K B hK D) (c.basePoint B hK hL)
  (c.sourcePoint B hK hL) (c.projectionPoint B hL) (c.siteSquare B hK hL)
  (c.targetPoint B hK hL) (c.targetPoint_over B hK hL)

abbrev sourceRepresentable :=
  Functor.relativelyRepresentable.map yoneda (sourceMap K B hK D)

/-- The physical curve and the chosen native source are canonically isomorphic. -/
def originalSourceIso : c.source ≅
    (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj
      (RelativeCoverSchemeEvaluation.source (sourceMap K B hK D) (targetMap K B hK D)
        (c.nativeFamily B hK hL) (sourceRepresentable B hK (D := D))) :=
  RelativeCoverOfOriginalSquare.originalSourceIso
    (sourceMap K B hK D) (targetMap K B hK D) (c.basePoint B hK hL)
    (c.sourcePoint B hK hL) (c.projectionPoint B hL) (c.siteSquare B hK hL)
    (c.targetPoint B hK hL) (c.targetPoint_over B hK hL) (sourceRepresentable B hK (D := D))

abbrev nativeProjection :
    (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj
      (RelativeCoverSchemeEvaluation.source (sourceMap K B hK D) (targetMap K B hK D)
        (c.nativeFamily B hK hL) (sourceRepresentable B hK (D := D))) ⟶ Spec (.of L) :=
  FixedDegreeCoverCurveGraphAdapter.totalProjection
    (sourceMap K B hK D) (targetMap K B hK D) (c.nativeFamily B hK hL)
    (sourceRepresentable B hK (D := D))

theorem originalSourceIso_projection :
    (c.originalSourceIso B hK hL).hom ≫ c.nativeProjection B hK hL = c.projection :=
  RelativeCoverOfOriginalSquare.originalSourceIso_projection
    (sourceMap K B hK D) (targetMap K B hK D) (c.basePoint B hK hL)
    (c.sourcePoint B hK hL) (c.projectionPoint B hL) (c.siteSquare B hK hL)
    (c.targetPoint B hK hL) (c.targetPoint_over B hK hL) (sourceRepresentable B hK (D := D))

theorem originalSourceIso_evaluation :
    (c.originalSourceIso B hK hL).hom ≫
      (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
        (RelativeCoverSchemeEvaluation.evaluation (sourceMap K B hK D) (targetMap K B hK D)
          (c.nativeFamily B hK hL) (sourceRepresentable B hK (D := D))) = c.originalTargetMap :=
  RelativeCoverOfOriginalSquare.originalSourceIso_evaluation
    (sourceMap K B hK D) (targetMap K B hK D) (c.basePoint B hK hL)
    (c.sourcePoint B hK hL) (c.projectionPoint B hL) (c.siteSquare B hK hL)
    (c.targetPoint B hK hL) (c.targetPoint_over B hK hL) (sourceRepresentable B hK (D := D))

abbrev nativeGroundMap : Spec (.of L) ⟶ Spec (.of K) :=
  FixedDegreeCoverCurveGraphAdapter.originalGroundMap
    (sourceMap K B hK D) (targetMap K B hK D) (c.nativeFamily B hK hL) K D.structureMap
abbrev nativeLineMap := FixedDegreeCoverCurveGraphAdapter.originalLineMap
  (sourceMap K B hK D) (targetMap K B hK D) (c.nativeFamily B hK hL)
  (sourceRepresentable B hK (D := D)) K
  (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap)

theorem nativeGroundMap_eq : c.nativeGroundMap B hK hL = coefficient := by
  change (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
      (yoneda.preimage (yoneda.map (c.basePoint B hK hL))) ≫ D.structureMap = coefficient
  rw [Functor.preimage_map]
  exact c.coefficient_triangle

theorem nativeLineMap_over :
    c.nativeLineMap B hK hL ≫ toBase K =
      c.nativeProjection B hK hL ≫ c.nativeGroundMap B hK hL :=
  FixedDegreeCoverCurveGraphAdapter.originalLineMap_over
    (sourceMap K B hK D) (targetMap K B hK D) (c.nativeFamily B hK hL)
    (sourceRepresentable B hK (D := D)) K D.structureMap
    (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap)
    (ConstantProjectiveLinePolarization.originalSquare K D.structureMap).w

/-- The true native field fibre at identity has the SAME physical source. -/
def fieldIso : c.source ≅ pullback (c.nativeProjection B hK hL) (𝟙 (Spec (.of L))) :=
  (IsPullback.of_horiz_isIso (fst := (c.originalSourceIso B hK hL).hom)
    (snd := c.projection) (f := c.nativeProjection B hK hL) (g := 𝟙 (Spec (.of L)))
    ⟨by simpa only [Category.comp_id] using c.originalSourceIso_projection B hK hL⟩).isoPullback

theorem fieldIso_toSource :
    (c.fieldIso B hK hL).hom ≫ pullback.fst (c.nativeProjection B hK hL) (𝟙 _) =
      (c.originalSourceIso B hK hL).hom :=
  IsPullback.isoPullback_hom_fst _

theorem fieldIso_over :
    (c.fieldIso B hK hL).hom ≫ pullback.snd (c.nativeProjection B hK hL) (𝟙 _) = c.projection :=
  IsPullback.isoPullback_hom_snd _

abbrev nativeFieldMap := ConstantP1CoverBaseChange.fieldMap K (c.nativeProjection B hK hL)
  (c.nativeGroundMap B hK hL) (c.nativeLineMap B hK hL) (c.nativeLineMap_over B hK hL)
  L (𝟙 (Spec (.of L)))

/-- Equality of the physical and native cover maps follows from the true
projective-space base-change square, including both of its projections. -/
theorem fieldIso_evaluation :
    (c.fieldIso B hK hL).hom ≫ c.nativeFieldMap B hK hL = c.lineMap := by
  have hc : (𝟙 (Spec (.of L))) ≫ c.nativeGroundMap B hK hL = coefficient := by
    rw [Category.id_comp, c.nativeGroundMap_eq]
  have hl := ConstantP1CoverBaseChange.fieldMap_toOriginal K (c.nativeProjection B hK hL)
    (c.nativeGroundMap B hK hL) (c.nativeLineMap B hK hL) (c.nativeLineMap_over B hK hL)
    L (𝟙 (Spec (.of L)))
  rw [hc] at hl
  apply (isPullback_projectiveSpaceOverMap 1 coefficient).hom_ext
  · calc
      ((c.fieldIso B hK hL).hom ≫ c.nativeFieldMap B hK hL) ≫
          projectiveSpaceOverMap 1 coefficient =
        (c.fieldIso B hK hL).hom ≫
          (pullback.fst (c.nativeProjection B hK hL) (𝟙 _) ≫ c.nativeLineMap B hK hL) := by
            rw [Category.assoc, hl]
      _ = (c.originalSourceIso B hK hL).hom ≫ c.nativeLineMap B hK hL := by
        rw [← Category.assoc, c.fieldIso_toSource]
      _ = c.originalTargetMap ≫ ConstantProjectiveLinePolarization.toGroundLine K D.structureMap := by
        change (c.originalSourceIso B hK hL).hom ≫
          ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map
            (RelativeCoverSchemeEvaluation.evaluation _ _ _ _) ≫ _) = _
        rw [← Category.assoc, c.originalSourceIso_evaluation]
      _ = c.lineMap ≫ projectiveSpaceOverMap 1 coefficient := c.originalTargetMap_toLine
  · change ((c.fieldIso B hK hL).hom ≫ c.nativeFieldMap B hK hL) ≫ toBase L =
      c.lineMap ≫ toBase L
    rw [Category.assoc, ConstantP1CoverBaseChange.fieldMap_over, c.fieldIso_over,
      c.lineMap_over]

theorem nativeFieldMap_eq : c.nativeFieldMap B hK hL = (c.fieldIso B hK hL).inv ≫ c.lineMap := by
  rw [← c.fieldIso_evaluation B hK hL, Iso.inv_hom_id_assoc]

instance nativeField_isCurve :
    IsCurve L (pullback.snd (c.nativeProjection B hK hL) (𝟙 (Spec (.of L)))) :=
  CurveTargetIsoDegree.isCurve _ c.projection (c.fieldIso B hK hL).symm (by
    change (c.fieldIso B hK hL).inv ≫ c.projection = _
    rw [← c.fieldIso_over B hK hL, Iso.inv_hom_id_assoc])

theorem nativeField_nonconstant :
    ¬ ∃ y : Line L, ∀ a : (pullback (c.nativeProjection B hK hL) (𝟙 _) : Scheme.{u}),
      (c.nativeFieldMap B hK hL).base a = y := by
  rw [c.nativeFieldMap_eq B hK hL]
  exact CurveSourceIsoDegree.nonconstant_precomp (c.fieldIso B hK hL).symm c.lineMap c.nonconstant

/-- The native field degree is the original physical native degree. -/
theorem nativeFieldDegree_eq :
    ConstantP1CoverDegreeBaseChange.fieldDegree K L (c.nativeProjection B hK hL)
      (c.nativeGroundMap B hK hL) (c.nativeLineMap B hK hL) (c.nativeLineMap_over B hK hL)
      (𝟙 (Spec (.of L))) (c.nativeField_nonconstant B hK hL) = c.nativeDegree := by
  have h := CurveSourceIsoDegree.curveMapDegree_precomp_iso
    (pullback.snd (c.nativeProjection B hK hL) (𝟙 (Spec (.of L)))) c.projection
    (toBase L) (c.fieldIso B hK hL).symm
    (by
      change (c.fieldIso B hK hL).inv ≫ c.projection = _
      rw [← c.fieldIso_over B hK hL, Iso.inv_hom_id_assoc])
    c.lineMap c.lineMap_over c.nonconstant
  letI : LocallyOfFiniteType c.lineMap :=
    locallyOfFiniteType_of_isCurve_comp L c.projection (toBase L) c.lineMap c.lineMap_over
  letI : IsDominant c.lineMap :=
    isDominant_of_not_constant L c.projection (toBase L) c.lineMap c.nonconstant
  letI : LocallyOfFiniteType (c.nativeFieldMap B hK hL) :=
    locallyOfFiniteType_of_isCurve_comp L
      (pullback.snd (c.nativeProjection B hK hL) (𝟙 (Spec (.of L))))
      (toBase L) (c.nativeFieldMap B hK hL)
      (ConstantP1CoverBaseChange.fieldMap_over _ _ _ _ _ _ _)
  letI : IsDominant (c.nativeFieldMap B hK hL) :=
    isDominant_of_not_constant L
      (pullback.snd (c.nativeProjection B hK hL) (𝟙 (Spec (.of L))))
      (toBase L) (c.nativeFieldMap B hK hL)
      (c.nativeField_nonconstant B hK hL)
  change degreeOver (c.nativeFieldMap B hK hL) = degreeOver c.lineMap
  change degreeOver ((c.fieldIso B hK hL).inv ≫ c.lineMap) = degreeOver c.lineMap at h
  simpa only [← c.nativeFieldMap_eq B hK hL] using h

/-- The section is constructed from the actual physical relative morphism. -/
def nativeSection := (relativeHomSections B integerBase (B.contains_integerBase)
  (yoneda.obj (sourceSite K B hK D)) (yoneda.obj (targetSite K B hK D))
  (yoneda.obj (baseSite K B hK D)) (yoneda.map (sourceMap K B hK D))
  (yoneda.map (targetMap K B hK D)) (schemeSpace (sourceSite K B hK D)).2
  (schemeSpace (targetSite K B hK D)).2 (schemeSpace (baseSite K B hK D)).2
  (integerSiteObject B (B.contains_integerBase) hL)).symm (c.nativeFamily B hK hL)

theorem familyOfSection_nativeSection :
    FixedDegreeCoverCurveGraphAdapter.familyOfSection (sourceMap K B hK D)
      (targetMap K B hK D) (c.nativeSection B hK hL) = c.nativeFamily B hK hL :=
  Equiv.apply_symm_apply _ _

/-- The actual graph adapter supplies membership from the transported
physical cover, with its computed degree and literal original lines. -/
theorem section_mem :
    c.nativeSection B hK hL ∈ (locus K B hK D c.nativeDegree).obj (op (integerSiteObject B (B.contains_integerBase) hL)) := by
  have hsource : FixedDegreeCoverCurveGraphAdapter.sourceGeometry (sourceMap K B hK D) D.line := by
    intro F _ V a q f _ sq
    exact D.fieldGeometry F V a q f sq
  let p := FixedDegreeCoverCurveGraphAdapter.familyOfSection (sourceMap K B hK D)
    (targetMap K B hK D) (c.nativeSection B hK hL)
  let fieldData (p : RelativeMorphism B integerBase (B.contains_integerBase)
      (yoneda.obj (sourceSite K B hK D)) (yoneda.obj (targetSite K B hK D))
      (yoneda.obj (baseSite K B hK D)) (yoneda.map (sourceMap K B hK D))
      (yoneda.map (targetMap K B hK D))
      (yoneda.obj (integerSiteObject B (B.contains_integerBase) hL))) : Prop :=
      ∃ hc : IsCurve L (pullback.snd (FixedDegreeCoverCurveGraphAdapter.totalProjection
        (sourceMap K B hK D) (targetMap K B hK D) p (sourceRepresentable B hK (D := D)))
          (𝟙 (Spec (.of L)))),
        letI := hc
        ∃ hn : ¬ ∃ y : Line L, ∀ a :
            (pullback (FixedDegreeCoverCurveGraphAdapter.totalProjection
              (sourceMap K B hK D) (targetMap K B hK D) p (sourceRepresentable B hK (D := D)))
              (𝟙 (Spec (.of L))) : Scheme.{u}),
          (ConstantP1CoverBaseChange.fieldMap K
            (FixedDegreeCoverCurveGraphAdapter.totalProjection (sourceMap K B hK D) (targetMap K B hK D)
              p (sourceRepresentable B hK (D := D)))
            (FixedDegreeCoverCurveGraphAdapter.originalGroundMap (sourceMap K B hK D)
              (targetMap K B hK D) p K D.structureMap)
            (FixedDegreeCoverCurveGraphAdapter.originalLineMap (sourceMap K B hK D) (targetMap K B hK D)
              p (sourceRepresentable B hK (D := D)) K
              (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap))
            (FixedDegreeCoverCurveGraphAdapter.originalLineMap_over (sourceMap K B hK D)
              (targetMap K B hK D) p (sourceRepresentable B hK (D := D)) K D.structureMap
              (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap)
              (ConstantProjectiveLinePolarization.originalSquare K D.structureMap).w)
            L (𝟙 (Spec (.of L)))).base a = y,
          ConstantP1CoverDegreeBaseChange.fieldDegree K L
            (FixedDegreeCoverCurveGraphAdapter.totalProjection (sourceMap K B hK D) (targetMap K B hK D)
              p (sourceRepresentable B hK (D := D)))
            (FixedDegreeCoverCurveGraphAdapter.originalGroundMap (sourceMap K B hK D)
              (targetMap K B hK D) p K D.structureMap)
            (FixedDegreeCoverCurveGraphAdapter.originalLineMap (sourceMap K B hK D) (targetMap K B hK D)
              p (sourceRepresentable B hK (D := D)) K
              (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap))
            (FixedDegreeCoverCurveGraphAdapter.originalLineMap_over (sourceMap K B hK D)
              (targetMap K B hK D) p (sourceRepresentable B hK (D := D)) K D.structureMap
              (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap)
              (ConstantProjectiveLinePolarization.originalSquare K D.structureMap).w)
            (𝟙 (Spec (.of L))) hn = c.nativeDegree
  have hraw : fieldData (c.nativeFamily B hK hL) := by
    exact ⟨c.nativeField_isCurve B hK hL, c.nativeField_nonconstant B hK hL,
      c.nativeFieldDegree_eq B hK hL⟩
  have hdata : fieldData p :=
    Eq.mpr (congrArg fieldData (c.familyOfSection_nativeSection B hK hL)) hraw
  obtain ⟨hc, hn, hd⟩ := hdata
  have hs := FixedDegreeCoverCurveGraphAdapter.section_mem_of_nonconstant_fieldCover
    (sourceMap K B hK D) (targetMap K B hK D) (sourceRepresentable B hK (D := D)) D.line
    (PolarizedCurveCoverScheme.targetSeparated B (targetContained K B hK D)
      (parameterContained K B hK D) (targetProjection K D))
    (PolarizedCurveCoverScheme.targetFinitePresentation B (targetContained K B hK D)
      (parameterContained K B hK D) (targetProjection K D))
    (PolarizedCurveCoverScheme.sourceFinitePresentation B (GenusNineCoverParameterSchemes.sourceContained K B hK D)
      (parameterContained K B hK D) D.projection)
    (PolarizedCurveCoverScheme.sourceFlat B (GenusNineCoverParameterSchemes.sourceContained K B hK D)
      (parameterContained K B hK D) D.projection)
    (PolarizedCurveCoverScheme.sourceProper B (GenusNineCoverParameterSchemes.sourceContained K B hK D)
      (parameterContained K B hK D) D.projection)
    K D.structureMap (ConstantProjectiveLinePolarization.toGroundLine K D.structureMap)
    (ConstantProjectiveLinePolarization.originalSquare K D.structureMap).w hsource
    (c.nativeSection B hK hL) L (𝟙 (Spec (.of L))) hc hn
  exact Eq.mp (congrArg (fun n : ℕ =>
    c.nativeSection B hK hL ∈ (locus K B hK D n).obj
      (op (integerSiteObject B (B.contains_integerBase) hL))) hd) hs

end PhysicalCover

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K))) {m : ℕ}
  (D : GenusNineGroundFieldPolarizedModels.Model.{u} K m)

/-- A physical cover lifts to a genuine parameter point of the SAME five
representers, retaining the original model point and actual native degree. -/
theorem exists_parameter_point
    (Y : Fin 5 → BigFppfOver B integerBase (B.contains_integerBase))
    (A : ∀ i, yoneda.obj (Y i) ⟶
      (locus K B hK D (BoundedPencilGraphPolynomial.degreeIndex i)).toFunctor)
    (q : ∀ i, Y i ⟶ baseSite K B hK D)
    (hA : ∀ i, IsIso (A i))
    (hq : ∀ i, A i ≫ GenusNineCoverParameterSchemes.projection K B hK D
      (BoundedPencilGraphPolynomial.degreeIndex i) = yoneda.map (q i))
    (L : Type u) [Field L] (hL : B.Contains (Spec (.of L)))
    (coefficient : Spec (.of L) ⟶ Spec (.of K)) (c : PhysicalCover D L coefficient)
    (hdegree : c.nativeDegree ≤ 5) :
    ∃ (i : Fin 5) (w : integerSiteObject B (B.contains_integerBase) hL ⟶ Y i),
      w ≫ q i = integerSiteMap B (B.contains_integerBase) hL
        (parameterContained K B hK D) c.modelPoint ∧
      (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map w ≫
        (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (q i) = c.modelPoint ∧
      BoundedPencilGraphPolynomial.degreeIndex i = c.nativeDegree := by
  obtain ⟨i, hi⟩ := BoundedPencilGraphPolynomial.exists_actual_degree_index
    c.projection c.lineMap c.lineMap_over c.nonconstant hdegree
  letI := hA i
  have hs : c.nativeSection B hK hL ∈
      (locus K B hK D (BoundedPencilGraphPolynomial.degreeIndex i)).obj
        (op (integerSiteObject B (B.contains_integerBase) hL)) := by
    rw [← hi]
    exact c.section_mem B hK hL
  have hq' : ((A i) ≫ (locus K B hK D (BoundedPencilGraphPolynomial.degreeIndex i)).ι) ≫
      relativeHomProjection B integerBase (B.contains_integerBase)
        (yoneda.obj (sourceSite K B hK D)) (yoneda.obj (targetSite K B hK D))
        (yoneda.obj (baseSite K B hK D)) (yoneda.map (sourceMap K B hK D))
        (yoneda.map (targetMap K B hK D)) (schemeSpace (sourceSite K B hK D)).2
        (schemeSpace (targetSite K B hK D)).2 (schemeSpace (baseSite K B hK D)).2 =
      yoneda.map (q i) := by
    simpa only [GenusNineCoverParameterSchemes.projection,
      PolarizedCurveCoverScheme.coverProjection, FixedDegreeCoverSpace.coverProjection,
      Category.assoc] using hq i
  obtain ⟨w, hw, hb⟩ := RelativeCoverOfOriginalSquare.exists_parameter_point
    (locus K B hK D (BoundedPencilGraphPolynomial.degreeIndex i)) _ (A i) (q i) hq'
    (c.nativeSection B hK hL) hs
  have hb' : w ≫ q i = c.basePoint B hK hL := by
    rw [hb, relativeHomProjection_app]
    simp only [PhysicalCover.nativeSection, Equiv.apply_symm_apply]
    rfl
  refine ⟨i, w, hb', ?_, hi.symm⟩
  calc
    _ = (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (w ≫ q i) :=
      (Functor.map_comp _ _ _).symm
    _ = (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (c.basePoint B hK hL) :=
      congrArg _ hb'
    _ = c.modelPoint := rfl

/-- One fixed set of five actual finite-type representing schemes covers
EVERY contained-field physical cover of this original model of degree at
most five. The representers are chosen before the field or physical cover. -/
theorem exists_five_parameterSchemes_covering :
    ∃ (Y : Fin 5 → BigFppfOver B integerBase (B.contains_integerBase))
      (A : ∀ i, yoneda.obj (Y i) ⟶
        (locus K B hK D (BoundedPencilGraphPolynomial.degreeIndex i)).toFunctor)
      (q : ∀ i, Y i ⟶ baseSite K B hK D),
      (∀ i, IsIso (A i)) ∧
      (∀ i, A i ≫ GenusNineCoverParameterSchemes.projection K B hK D
        (BoundedPencilGraphPolynomial.degreeIndex i) = yoneda.map (q i)) ∧
      (∀ i, Space.QuasiCompactFiniteType
        ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (q i))) ∧
      (∀ (L : Type u) [Field L] (hL : B.Contains (Spec (.of L)))
        (coefficient : Spec (.of L) ⟶ Spec (.of K)) (c : PhysicalCover D L coefficient),
        c.nativeDegree ≤ 5 →
        ∃ (i : Fin 5) (w : integerSiteObject B (B.contains_integerBase) hL ⟶ Y i),
          w ≫ q i = integerSiteMap B (B.contains_integerBase) hL
            (parameterContained K B hK D) c.modelPoint ∧
          (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map w ≫
            (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (q i) = c.modelPoint ∧
          BoundedPencilGraphPolynomial.degreeIndex i = c.nativeDegree) := by
  obtain ⟨Y, A, q, hA, hq, hft⟩ := exists_five_parameterSchemes K B hK D
  refine ⟨Y, A, q, hA, hq, hft, ?_⟩
  intro L _ hL coefficient c hd
  exact exists_parameter_point K B hK D Y A q hA hq L hL coefficient c hd

end M9Native.GenusNinePhysicalCoverParameterPoint
end

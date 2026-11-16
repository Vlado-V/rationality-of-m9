module

public import M9StacksIntegration.CurveSchemePowerSeries
public import M9StacksIntegration.Private.FormalHullEquivalence
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationThickening
public import StacksFrontier.Deformation.FormalObject.VersalEquivalence
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation

/-!
# The constructed formal scheme hull as an actual curve-stack deformation

Original 0DZU constructs the actual equivalence from flat scheme
deformations to deformations of the original curve-family point. Applying
it level by level preserves the actual formal base and actual versality.
No formal-deformation identification, formal object or dimension is an
input. The further small-model/field-base transport remains separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin Deformation.Examples

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber

universe u

namespace M9Native.CurveFormalToCurves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

theorem originalCurveProper : IsProper (Over.mk f).hom :=
  inferInstanceAs (IsProper f)

attribute [local instance] originalCurveProper

/-- The literal terminal integer-base map; it is definitionally the map used
by the later field-base VersalSituation. No algebraicity input is needed here. -/
def integerBaseArrow : B.obj hk ⟶ B.obj hZ :=
  ObjectProperty.homMk (specULiftZIsTerminal.from _)

/-- The original native curve-point predeformation category, over Artin k-algebras. -/
abbrev pointPredeformation :=
  curvesPredeformation B hZ (Over.mk f) hk
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    (B.inclusion.map (integerBaseArrow B hZ hk))

/-- Its original predeformation structure comes from the original fibre structure. -/
def predeformationStructure :
    letI := (pointPredeformation B hZ hk f).category
    IsPredeformationCategory (pointPredeformation B hZ hk f).projection := by
  letI := (pointPredeformation B hZ hk f).category
  exact predeformationCategory_isPredeformationCategory B hZ
    (B.inclusion.map (integerBaseArrow B hZ hk))
    (curvesFiberedCategory B hZ).val.p
    (curveFamilyOfScheme (Over.mk f) B hZ hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le)
    (curvesToSchemesOver_obj_curveFamilyOfScheme (Over.mk f) B hZ hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk)))
    (curvesFiberedCategory B hZ).property

/-- Apply the actual original 0DZU comparison to the actual constructed formal hull. -/
def formalCurveHull :
    letI := (pointPredeformation B hZ hk f).category
    FormalObject (pointPredeformation B hZ hk f).projection := by
  letI := (pointPredeformation B hZ hk f).category
  exact (formalObjectMapOfCompEq
    (schemeDeformationToCurves B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk)))
    (schemeDeformationToCurvesBased B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk))).w).obj
      (CurveSchemePowerSeries.formalHull f)

/-- The original curve-stack formal object has exactly the constructed formal base. -/
theorem formalCurveHull_base :
    (formalCurveHull B hZ hk f).base = (CurveSchemePowerSeries.formalHull f).base := rfl

/-- Original 0DZU and the genuine levelwise formal functor preserve actual versality. -/
theorem formalCurveHull_isVersal :
    letI := (pointPredeformation B hZ hk f).category
    IsVersal (predeformationStructure B hZ hk f).cofibered (formalCurveHull B hZ hk f) := by
  letI := (pointPredeformation B hZ hk f).category
  exact isVersal_formalObjectMapOfCompEq
    (schemeDeformationToCurves B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk)))
    (schemeDeformationToCurvesBased B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk))).w
    (schemeDeformation_cofibered (Over.mk f))
    (predeformationStructure B hZ hk f).cofibered
    (CurveSchemePowerSeries.formalHull f) (CurveSchemePowerSeries.formalHull_isHull f).1

/-- Original 0DZU also preserves the actual bijective hull differential,
proved on the original fibre classes of the two deformation categories. -/
theorem formalCurveHull_hasBijectiveDifferential :
    letI := (pointPredeformation B hZ hk f).category
    HasBijectiveDifferential (predeformationStructure B hZ hk f).cofibered
      (formalCurveHull B hZ hk f) := by
  letI := (pointPredeformation B hZ hk f).category
  exact FormalHullEquivalence.hasBijectiveDifferential_map
    (schemeDeformationToCurves B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk)))
    (schemeDeformationToCurvesBased B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk))).w
    (schemeDeformation_cofibered (Over.mk f))
    (predeformationStructure B hZ hk f).cofibered
    (CurveSchemePowerSeries.formalHull f) (CurveSchemePowerSeries.formalHull_isHull f).2

/-- The formal object in the original curve-point deformation category is
an actual hull, with both versality and its bijective differential proved. -/
theorem formalCurveHull_isHull :
    letI := (pointPredeformation B hZ hk f).category
    IsHull (predeformationStructure B hZ hk f).cofibered
      (formalCurveHull B hZ hk f) := by
  letI := (pointPredeformation B hZ hk f).category
  exact ⟨formalCurveHull_isVersal B hZ hk f,
    formalCurveHull_hasBijectiveDifferential B hZ hk f⟩

/-- Genus nine derives faithfulness of the original rigidified curve-point
projection by the actual original 0DZU equivalence, not by faithfulness of
the global stack of curves. -/
theorem projection_faithful_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    letI := (pointPredeformation B hZ hk f).category
    (pointPredeformation B hZ hk f).projection.Faithful := by
  letI := (pointPredeformation B hZ hk f).category
  letI : (schemeDeformationCategoryProjection (Λ := k) (Over.mk f)).Faithful :=
    CurveSchemeProrepresentability.structure_faithful f hg
  letI : (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := k) (Over.mk f))).p.Faithful :=
    CurveSchemeProrepresentability.structure_faithful f hg
  exact FormalHullEquivalence.faithful_target
    (schemeDeformationToCurves B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk)))
    (schemeDeformationToCurvesBased B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (integerBaseArrow B hZ hk))).w
    (schemeDeformation_cofibered (Over.mk f))

/-- The actual curve-point formal object has actual formal-ring dimension24. -/
theorem formalCurveHull_krullDimension_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    ringKrullDim (formalCurveHull B hZ hk f).base = (24 : WithBot ℕ∞) := by
  rw [formalCurveHull_base]
  exact CurveSchemePowerSeries.formalHull_krullDimension_genus_nine f hg

/-- The actual hull derives Schlessinger S2 for the actual functor of
classes at the original curve-family point. -/
theorem associatedTangentS2 :
    letI := (pointPredeformation B hZ hk f).category
    SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses
        (BasedCategory.ofFunctor (pointPredeformation B hZ hk f).projection)
        (predeformationStructure B hZ hk f).cofibered)) := by
  letI := (pointPredeformation B hZ hk f).category
  let hp := predeformationStructure B hZ hk f
  exact schlessingerConditionS2_of_isIsomorphismClasses _ hp.cofibered
    (schlessingerConditionS2_of_versal_bijectiveDifferential
      (pointPredeformation B hZ hk f).projection hp (formalCurveHull B hZ hk f)
      (formalCurveHull_isVersal B hZ hk f)
      (formalCurveHull_hasBijectiveDifferential B hZ hk f)) (Or.inl hp)

/-- The original curve-point deformation tangent has actual canonical
k-linear dimension24; no tangent identification or dimension is supplied. -/
theorem tangent_finrank_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    letI := (pointPredeformation B hZ hk f).category
    letI : Fact (IsPredeformationCategory
      (BasedCategory.ofFunctor (pointPredeformation B hZ hk f).projection).p) :=
      ⟨predeformationStructure B hZ hk f⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses
        (BasedCategory.ofFunctor (pointPredeformation B hZ hk f).projection)
        (predeformationStructure B hZ hk f).cofibered))) :=
      ⟨associatedTangentS2 B hZ hk f⟩
    Module.finrank k (tangentSpaceArtinian k k
      (isomorphismClasses
        (BasedCategory.ofFunctor (pointPredeformation B hZ hk f).projection)
        (predeformationStructure B hZ hk f).cofibered)) = 24 := by
  letI := (pointPredeformation B hZ hk f).category
  let hp := predeformationStructure B hZ hk f
  letI : Fact (IsPredeformationCategory
      (BasedCategory.ofFunctor (pointPredeformation B hZ hk f).projection).p) := ⟨hp⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses
      (BasedCategory.ofFunctor (pointPredeformation B hZ hk f).projection) hp.cofibered))) :=
      ⟨associatedTangentS2 B hZ hk f⟩
  have hsource : Module.finrank k (tangentSpaceArtinian k k
      (restrictedCoyoneda (formalCurveHull B hZ hk f).base)) = 24 := by
    change Module.finrank k (tangentSpaceArtinian k k
      (restrictedCoyoneda (CurveSchemePowerSeries.formalHull f).base)) = 24
    exact CurveSchemePowerSeries.formalHull_tangent_finrank_genus_nine f hg
  exact (HullTangentComparison.tangentLinearEquiv
    (BasedCategory.ofFunctor (pointPredeformation B hZ hk f).projection) hp
    (associatedTangentS2 B hZ hk f) (formalCurveHull B hZ hk f)
    (formalCurveHull_hasBijectiveDifferential B hZ hk f)).finrank_eq.symm.trans hsource

/-- Actual smooth source curves have unobstructed original curve-point
deformations, derived from the genuine formal hull and its constructed
power-series model. -/
theorem unobstructed :
    letI := (pointPredeformation B hZ hk f).category
    IsSmooth (baseProjection (pointPredeformation B hZ hk f).projection) := by
  letI := (pointPredeformation B hZ hk f).category
  apply (isSmooth_baseProjection_iff_powerSeries
    (predeformationStructure B hZ hk f) (formalCurveHull B hZ hk f)
    (formalCurveHull_isVersal B hZ hk f)
    (CurveSchemeProrepresentability.classical_baseField k)).mpr
  exact ⟨CurveSchemePowerSeries.variableCount f,
    ⟨CurveSchemePowerSeries.powerSeriesEquiv f⟩⟩

end M9Native.CurveFormalToCurves

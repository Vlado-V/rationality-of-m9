module

public import M9StacksIntegration.CurveFormalToCurves
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.Deformation.Artin.Predeformation.Transport

/-!
# The actual native small-model point of an original curve

The original native hom-shrink equivalence transports the constructed original
curve-point hull to exactly the small model used by `curvesAlgebraicStack`.
The base ring, genuine hull, and marked faithfulness are preserved. This is
a construction in the original native categories; algebraicity is not an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin Deformation.Examples

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber

universe u

namespace M9Native.CurveFormalSmall

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]

theorem originalCurveProper : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
attribute [local instance] originalCurveProper

/-- The actual image of the original proper curve in the native hom-shrunk category. -/
abbrev point : (curvesSmallBased B hZ).obj :=
  (curvesSmallEquivalenceOver B hZ).hom.functor.obj
    (curveFamilyOfScheme (Over.mk f) B hZ hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le)

/-- The native small point lies over the original field spectrum and integer-base map. -/
theorem point_lies_over :
    ((curvesSmallBased B hZ).p ⋙ Over.post B.inclusion).obj (point B hZ hk f) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫
        B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) :=
  (transport_obj_eq B hZ (curvesFiberedCategory B hZ).val.p
    (curvesSmallBased B hZ).p _ (curvesSmallEquivalenceOver B hZ).hom.w _).trans
      (curvesToSchemesOver_obj_curveFamilyOfScheme (Over.mk f) B hZ hk
        (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)))

/-- The literal native predeformation category of that actual small-model point. -/
abbrev predeformation :=
  predeformationCategory (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
    ((curvesSmallBased B hZ).p ⋙ Over.post B.inclusion)
    (point B hZ hk f) (point_lies_over B hZ hk f)

/-- Its genuine predeformation structure comes from the native fibre structure. -/
def predeformationStructure :
    letI := (predeformation B hZ hk f).category
    IsPredeformationCategory (predeformation B hZ hk f).projection := by
  letI := (predeformation B hZ hk f).category
  exact predeformationCategory_isPredeformationCategory B hZ
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
    (curvesSmallBased B hZ).p (point B hZ hk f) (point_lies_over B hZ hk f)
    (isFiberedInGroupoids_curvesSmall B hZ)

variable [Smooth f]

/-- The actual original hom-shrink equivalence induces the actual strict
comparison of the two original curve-point deformation categories. -/
def comparison :
    letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
    letI := (predeformation B hZ hk f).category
    StacksRepresentableCFG.EquivalenceOver
      (CurveFormalToCurves.pointPredeformation B hZ hk f).projection
      (predeformation B hZ hk f).projection := by
  letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
  letI := (predeformation B hZ hk f).category
  exact predeformationEquivalenceOfEquivalenceOver B hZ
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
    (curvesFiberedCategory B hZ).val.p (curvesSmallBased B hZ).p
    (curveFamilyOfScheme (Over.mk f) B hZ hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le)
    (curvesToSchemesOver_obj_curveFamilyOfScheme (Over.mk f) B hZ hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)))
    (curvesFiberedCategory B hZ).property (isFiberedInGroupoids_curvesSmall B hZ)
    (curvesSmallEquivalenceOver B hZ)

/-- The original constructed hull, transported to the actual native small-model point. -/
def formalHull :
    letI := (predeformation B hZ hk f).category
    Deformation.FormalObject (predeformation B hZ hk f).projection := by
  letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
  letI := (predeformation B hZ hk f).category
  let E := comparison B hZ hk f
  exact (formalObjectMapOfCompEq E.hom.functor E.hom.w).obj
    (CurveFormalToCurves.formalCurveHull B hZ hk f)

/-- The actual same original complete local k-algebra is retained. -/
theorem formalHull_base :
    (formalHull B hZ hk f).base = (CurveSchemePowerSeries.formalHull f).base := rfl

/-- Both actual components of the native hull condition are preserved. -/
theorem formalHull_isHull :
    letI := (predeformation B hZ hk f).category
    IsHull (predeformationStructure B hZ hk f).cofibered (formalHull B hZ hk f) := by
  letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
  letI := (predeformation B hZ hk f).category
  let E := comparison B hZ hk f
  letI : E.hom.functor.IsEquivalence := E.isEquivalence_hom_functor
  exact ⟨isVersal_formalObjectMapOfCompEq E.hom.functor E.hom.w
      (CurveFormalToCurves.predeformationStructure B hZ hk f).cofibered
      (predeformationStructure B hZ hk f).cofibered
      (CurveFormalToCurves.formalCurveHull B hZ hk f)
      (CurveFormalToCurves.formalCurveHull_isVersal B hZ hk f),
    FormalHullEquivalence.hasBijectiveDifferential_map E.hom.functor E.hom.w
      (CurveFormalToCurves.predeformationStructure B hZ hk f).cofibered
      (predeformationStructure B hZ hk f).cofibered
      (CurveFormalToCurves.formalCurveHull B hZ hk f)
      (CurveFormalToCurves.formalCurveHull_hasBijectiveDifferential B hZ hk f)⟩

/-- Faithfulness is derived only for the original marked deformation projection. -/
theorem projection_faithful_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    letI := (predeformation B hZ hk f).category
    (predeformation B hZ hk f).projection.Faithful := by
  letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
  letI := (predeformation B hZ hk f).category
  letI : (CurveFormalToCurves.pointPredeformation B hZ hk f).projection.Faithful :=
    CurveFormalToCurves.projection_faithful_genus_nine B hZ hk f hg
  let E := comparison B hZ hk f
  letI : E.hom.functor.IsEquivalence := E.isEquivalence_hom_functor
  exact FormalHullEquivalence.faithful_target E.hom.functor E.hom.w
    (CurveFormalToCurves.predeformationStructure B hZ hk f).cofibered

/-- The actual native small-point formal base has Krull dimension24. -/
theorem formalHull_krullDimension_genus_nine [IsAlgClosed k] (hg : genus f = 9) :
    ringKrullDim (formalHull B hZ hk f).base = (24 : WithBot ℕ∞) := by
  rw [formalHull_base]
  exact CurveSchemePowerSeries.formalHull_krullDimension_genus_nine f hg

/-- The native small-point deformation problem is genuinely unobstructed. -/
theorem unobstructed :
    letI := (predeformation B hZ hk f).category
    IsSmooth (baseProjection (predeformation B hZ hk f).projection) := by
  letI := (predeformation B hZ hk f).category
  apply (isSmooth_baseProjection_iff_powerSeries
    (predeformationStructure B hZ hk f) (formalHull B hZ hk f)
    (formalHull_isHull B hZ hk f).1
    (CurveSchemeProrepresentability.classical_baseField k)).mpr
  exact ⟨CurveSchemePowerSeries.variableCount f,
    ⟨CurveSchemePowerSeries.powerSeriesEquiv f⟩⟩

end M9Native.CurveFormalSmall

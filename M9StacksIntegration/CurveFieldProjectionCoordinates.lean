module

public import M9StacksIntegration.CurveFieldTargetComparison
public import M9StacksIntegration.PointedIndexTransport

/-!
# Literal marked coordinates of the genuine field-to-small projection

The native base-change comparison is followed only by equality transport
of the actual structural index. The original family and marking survive
that transport; the coordinate laws are derived from equality elimination.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u
namespace M9Native.CurveFieldProjectionCoordinates

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  (iS : Spec (.of k) ⟶ Spec (.of K))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

local instance originalCurveProper : IsProper (Over.mk f).hom :=
  inferInstanceAs (IsProper f)

open CurveFieldTargetComparison

abbrev smallProjection := Stack.algebraicStackBaseChangeProjection B (Spec (.of K)) integerBase
  hK hZ (baseArrow B hZ hK) (integerStack B hZ hAlg)

abbrev rawSmall := predeformationCategory
  (iS ≫ B.inclusion.map (baseArrow B hZ hK))
  ((integerStack B hZ hAlg).val.val.p ⋙ Over.post B.inclusion)
  (CurveFormalSmall.point B hZ hk f) (integerPoint_lies_over B hZ hK hAlg hk iS f)

/-- The actual native projection before the proved terminal-index transport. -/
def rawComparison :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    letI := (rawSmall B hZ hK hAlg hk iS f).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformation B hZ hK hAlg hk iS f).projection
      (rawSmall B hZ hK hAlg hk iS f).projection := by
  letI := (predeformation B hZ hK hAlg hk iS f).category
  letI := (rawSmall B hZ hK hAlg hk iS f).category
  have E := AlgebraicStackBaseChangeEquivalence.equivalence B (Spec (.of K)) integerBase
    hK hZ (baseArrow B hZ hK) (integerStack B hZ hAlg) iS
    (fieldPoint B hZ hK hAlg hk iS f)
    (fieldPoint_lies_over B hZ hK hAlg hk iS f)
  dsimp only [fieldPoint] at E
  simp only [Stack.algebraicStackBaseChangeProjection_obj_lift] at E
  exact E

/-- The true second stage changes only the equal structural-map index. -/
abbrev indexComparison := PointedIndexTransport.equivalence
  ((integerStack B hZ hAlg).val.val.p ⋙ Over.post B.inclusion)
  (CurveFormalSmall.point B hZ hk f)
  (iS ≫ B.inclusion.map (baseArrow B hZ hK))
  (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
  (integerPoint_lies_over B hZ hK hAlg hk iS f)
  (CurveFormalSmall.point_lies_over B hZ hk f)
  (integerBaseArrow_comp B hZ hK hk iS)

omit [Smooth f] in
/-- The original comparison is precisely native projection followed by
this genuine equality transport, with no extra model identification. -/
theorem comparison_eq :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    letI := (rawSmall B hZ hK hAlg hk iS f).category
    letI := (CurveFormalSmall.predeformation B hZ hk f).category
    comparison B hZ hK hAlg hk iS f =
      (rawComparison B hZ hK hAlg hk iS f).trans
        (indexComparison B hZ hK hAlg hk iS f) := rfl

omit [Smooth f] in
/-- The native projection retains the literal original family object. -/
theorem raw_object_point
    (d : (predeformation B hZ hK hAlg hk iS f).carrier) :
    ((rawSmall B hZ hK hAlg hk iS f).objects
      ((rawComparison B hZ hK hAlg hk iS f).hom.functor.obj d)).point =
      (smallProjection B hZ hK hAlg).obj
        ((predeformation B hZ hK hAlg hk iS f).objects d).point := rfl

omit [Smooth f] in
/-- Its marking is the image of the same original marking. -/
theorem raw_object_arrow
    (d : (predeformation B hZ hK hAlg hk iS f).carrier) :
    ((rawSmall B hZ hK hAlg hk iS f).objects
      ((rawComparison B hZ hK hAlg hk iS f).hom.functor.obj d)).arrow =
      (smallProjection B hZ hK hAlg).map
        ((predeformation B hZ hK hAlg hk iS f).objects d).arrow := rfl

omit [Smooth f] in
/-- The final comparison retains the SAME original family after the
proved terminal-index identification. -/
theorem object_point
    (d : (predeformation B hZ hK hAlg hk iS f).carrier) :
    ((CurveFormalSmall.predeformation B hZ hk f).objects
      ((comparison B hZ hK hAlg hk iS f).hom.functor.obj d)).point =
      (smallProjection B hZ hK hAlg).obj
        ((predeformation B hZ hK hAlg hk iS f).objects d).point := by
  let := (predeformation B hZ hK hAlg hk iS f).category
  let := (rawSmall B hZ hK hAlg hk iS f).category
  let := (CurveFormalSmall.predeformation B hZ hk f).category
  rw [comparison_eq]
  exact PointedIndexTransport.object_point
    ((integerStack B hZ hAlg).val.val.p ⋙ Over.post B.inclusion)
    (CurveFormalSmall.point B hZ hk f)
    (iS ≫ B.inclusion.map (baseArrow B hZ hK))
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
    (integerPoint_lies_over B hZ hK hAlg hk iS f)
    (CurveFormalSmall.point_lies_over B hZ hk f)
    (integerBaseArrow_comp B hZ hK hk iS)
    ((rawComparison B hZ hK hAlg hk iS f).hom.functor.obj d)

omit [Smooth f] in
/-- The marking is the original projected marking with only the proved
literal endpoint identification. -/
theorem object_arrow
    (d : (predeformation B hZ hK hAlg hk iS f).carrier) :
    ((CurveFormalSmall.predeformation B hZ hk f).objects
      ((comparison B hZ hK hAlg hk iS f).hom.functor.obj d)).arrow =
      (smallProjection B hZ hK hAlg).map
        ((predeformation B hZ hK hAlg hk iS f).objects d).arrow ≫
      eqToHom (object_point B hZ hK hAlg hk iS f d).symm := by
  let := (predeformation B hZ hK hAlg hk iS f).category
  let := (rawSmall B hZ hK hAlg hk iS f).category
  let := (CurveFormalSmall.predeformation B hZ hk f).category
  exact PointedIndexTransport.object_arrow
    ((integerStack B hZ hAlg).val.val.p ⋙ Over.post B.inclusion)
    (CurveFormalSmall.point B hZ hk f)
    (iS ≫ B.inclusion.map (baseArrow B hZ hK))
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
    (integerPoint_lies_over B hZ hK hAlg hk iS f)
    (CurveFormalSmall.point_lies_over B hZ hk f)
    (integerBaseArrow_comp B hZ hK hk iS)
    ((rawComparison B hZ hK hAlg hk iS f).hom.functor.obj d)

end M9Native.CurveFieldProjectionCoordinates

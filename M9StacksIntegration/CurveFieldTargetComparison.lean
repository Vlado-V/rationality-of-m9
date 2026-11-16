module

public import M9StacksIntegration.CurveFormalSmall
public import M9StacksIntegration.Private.AlgebraicStackBaseChangeEquivalence

/-!
# The actual curve deformation problem over a ground-field base

The curve has coefficient field k and the ground field is K. The actual
map Spec k to Spec K is retained throughout. The original 0DZU functor,
the original small-model comparison, and the inverse of the genuine
base-change projection are composed over the unchanged Artin k-category.

Algebraicity of the ORIGINAL Curves category is an explicit remaining
geometric input. Neither an equivalence nor a tangent comparison is an
input. No finiteness of a map to the integer spectrum is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber

universe u
namespace M9Native.CurveFieldTargetComparison

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))

/-- The actual terminal integer-base map of the original ground field. -/
abbrev baseArrow : B.obj hK ⟶ B.obj hZ :=
  CurveFormalToCurves.integerBaseArrow B hZ hK

variable
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- The original small Curves presentation, with its genuine algebraicity input. -/
abbrev integerStack : Stack.AlgebraicStacks.{u,u+1} B integerBase hZ :=
  curvesAlgebraicStack B hZ hAlg

/-- The actual base change to the specified original ground field. -/
abbrev fieldStack : Stack.AlgebraicStacks.{u,u+1} B (Spec (.of K)) hK :=
  Stack.algebraicStackBaseChange B (Spec (.of K)) integerBase hK hZ
    (baseArrow B hZ hK) (integerStack B hZ hAlg)

variable {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  (iS : Spec (.of k) ⟶ Spec (.of K))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

local instance originalCurveProper : IsProper (Over.mk f).hom :=
  inferInstanceAs (IsProper f)

/-- The actual composed base map is the original terminal integer map,
without identifying the coefficient field with the ground field. -/
theorem integerBaseArrow_comp :
    iS ≫ B.inclusion.map (baseArrow B hZ hK) =
      B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk) :=
  specULiftZIsTerminal.hom_ext _ _

omit [Smooth f] in
/-- The original small point lies over the actual composed ground-base map. -/
theorem integerPoint_lies_over :
    ((integerStack B hZ hAlg).val.val.p ⋙ Over.post B.inclusion).obj
        (CurveFormalSmall.point B hZ hk f) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫
        (iS ≫ B.inclusion.map (baseArrow B hZ hK))) := by
  rw [integerBaseArrow_comp B hZ hK hk iS]
  exact CurveFormalSmall.point_lies_over B hZ hk f

/-- The genuine native base-change factor of that same original point. -/
def fieldFactor :=
  Stack.algebraicStackBaseChangeFactor B (Spec (.of K)) integerBase hK hZ
    (baseArrow B hZ hK) (integerStack B hZ hAlg) (CurveFormalSmall.point B hZ hk f)
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ iS))
    (by
      change _ = Over.mk ((Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ iS) ≫
        B.inclusion.map (baseArrow B hZ hK))
      simpa only [Category.assoc] using integerPoint_lies_over B hZ hK hAlg hk iS f)

/-- The actual point of Curves over the original ground field. -/
def fieldPoint : (fieldStack B hZ hK hAlg).val.val.obj :=
  Stack.algebraicStackBaseChangeLift B (Spec (.of K)) integerBase hK hZ
    (baseArrow B hZ hK) (integerStack B hZ hAlg) (CurveFormalSmall.point B hZ hk f)
    (fieldFactor B hZ hK hAlg hk iS f)

omit [Smooth f] in
/-- The point retains its actual coefficient-field-to-ground-field map. -/
theorem fieldPoint_lies_over :
    ((fieldStack B hZ hK hAlg).val.val.p ⋙ Over.post B.inclusion).obj
        (fieldPoint B hZ hK hAlg hk iS f) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ iS) :=
  Stack.algebraicStackBaseChangeLift_factor_post B (Spec (.of K)) integerBase hK hZ
    (baseArrow B hZ hK) (integerStack B hZ hAlg) (CurveFormalSmall.point B hZ hk f)
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ iS))
    (by
      change _ = Over.mk ((Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ iS) ≫
        B.inclusion.map (baseArrow B hZ hK))
      simpa only [Category.assoc] using integerPoint_lies_over B hZ hK hAlg hk iS f)

/-- The literal actual ground-field-stack point deformation category. -/
abbrev predeformation :=
  predeformationCategory iS
    ((fieldStack B hZ hK hAlg).val.val.p ⋙ Over.post B.inclusion)
    (fieldPoint B hZ hK hAlg hk iS f)
    (fieldPoint_lies_over B hZ hK hAlg hk iS f)

omit [Smooth f] in
/-- Its native predeformation structure uses the actual field-stack projection. -/
theorem predeformationStructure :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    IsPredeformationCategory (predeformation B hZ hK hAlg hk iS f).projection := by
  let := (predeformation B hZ hK hAlg hk iS f).category
  exact predeformationCategory_isPredeformationCategory B hK iS
    (fieldStack B hZ hK hAlg).val.val.p
    (fieldPoint B hZ hK hAlg hk iS f)
    (fieldPoint_lies_over B hZ hK hAlg hk iS f)
    (fieldStack B hZ hK hAlg).val.property

/-- The actual base-change projection is equivalent to the ORIGINAL small
point problem. Its inverse is supplied by genuine native arrow/object lifts. -/
def comparison :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    letI := (CurveFormalSmall.predeformation B hZ hk f).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformation B hZ hK hAlg hk iS f).projection
      (CurveFormalSmall.predeformation B hZ hk f).projection := by
  letI := (predeformation B hZ hK hAlg hk iS f).category
  letI := (CurveFormalSmall.predeformation B hZ hk f).category
  have E := AlgebraicStackBaseChangeEquivalence.equivalence B (Spec (.of K)) integerBase
    hK hZ (baseArrow B hZ hK) (integerStack B hZ hAlg) iS
    (fieldPoint B hZ hK hAlg hk iS f)
    (fieldPoint_lies_over B hZ hK hAlg hk iS f)
  dsimp only [fieldPoint] at E
  simp only [Stack.algebraicStackBaseChangeProjection_obj_lift] at E
  let Q := (integerStack B hZ hAlg).val.val.p ⋙ Over.post B.inclusion
  let a := iS ≫ B.inclusion.map (baseArrow B hZ hK)
  let y := CurveFormalSmall.point B hZ hk f
  have hy : Q.obj y = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ a) :=
    integerPoint_lies_over B hZ hK hAlg hk iS f
  let D := predeformationCategory a Q y hy
  letI := D.category
  let T : ∀ (j : Spec (.of k) ⟶ integerBase)
      (hj : Q.obj y = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ j)),
      a = j →
      letI := (predeformationCategory j Q y hj).category
      StacksRepresentableCFG.EquivalenceOver D.projection
        (predeformationCategory j Q y hj).projection := by
    intro j hj ha
    subst j
    exact StacksRepresentableCFG.EquivalenceOver.refl D.projection
  exact E.trans (T (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
    (CurveFormalSmall.point_lies_over B hZ hk f)
    (integerBaseArrow_comp B hZ hK hk iS))

/-- The genuine composite 0DZU, original small-model comparison, and
inverse ground-field base-change projection, all over Artin k-algebras. -/
def schemeEquivalence :
    letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
    letI := (CurveFormalSmall.predeformation B hZ hk f).category
    letI := (predeformation B hZ hK hAlg hk iS f).category
    StacksRepresentableCFG.EquivalenceOver
      (schemeDeformationCategoryProjection (Λ := k) (Over.mk f))
      (predeformation B hZ hK hAlg hk iS f).projection := by
  letI := (CurveFormalToCurves.pointPredeformation B hZ hk f).category
  letI := (CurveFormalSmall.predeformation B hZ hk f).category
  letI := (predeformation B hZ hK hAlg hk iS f).category
  let φ := schemeDeformationToCurvesBased B hZ (Over.mk f) hk
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))
  letI : φ.toFunctor.IsEquivalence :=
    inferInstanceAs (schemeDeformationToCurves B hZ (Over.mk f) hk
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk))).IsEquivalence
  let E := equivalenceOverOfCofibered (schemeDeformation_cofibered (Over.mk f))
    φ.toFunctor φ.w
  exact (E.trans (CurveFormalSmall.comparison B hZ hk f)).trans
    (comparison B hZ hK hAlg hk iS f).symm

/-- The actual composite as a based functor, with the original strict
Artin projection and original marking. -/
def basedComparison :
    letI := (predeformation B hZ hK hAlg hk iS f).category
    schemeDeformationBased (Λ := k) (Over.mk f) ⥤ᵇ
      BasedCategory.ofFunctor (predeformation B hZ hK hAlg hk iS f).projection := by
  letI := (predeformation B hZ hK hAlg hk iS f).category
  exact ⟨(schemeEquivalence B hZ hK hAlg hk iS f).hom.functor,
    (schemeEquivalence B hZ hK hAlg hk iS f).hom.w⟩

end M9Native.CurveFieldTargetComparison

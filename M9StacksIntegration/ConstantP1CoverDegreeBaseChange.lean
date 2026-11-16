module

public import M9StacksIntegration.ConstantP1CoverBaseChange

/-!
# Native curve degree on actual base-changed constant-P1 covers

The changed curve, genus and degree are derived from the genuine
pullback-pasting isomorphism. The field-valued point is arbitrary and
the original field and parameter maps are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] isCurve_projectiveSpaceOver_one

universe u

namespace M9Native.ConstantP1CoverDegreeBaseChange

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange

variable (K L : Type u) [Field K] [Field L] {X T P : Scheme.{u}}
  (p : X ⟶ T) (s : T ⟶ Spec (.of K))
  (g : X ⟶ Line K) (hg : g ≫ toBase K = p ≫ s)

/-- Degree on the literal native line over the actual test field, with
its original curve-to-field triangle. -/
def fieldDegree (i : Spec (.of L) ⟶ T) [IsCurve L (pullback.snd p i)]
    (hnc : ¬ ∃ y : Line L, ∀ c : (pullback p i : Scheme.{u}),
      (fieldMap K p s g hg L i).base c = y) : ℕ :=
  PencilDegreePullback.curveMapDegree (pullback.snd p i) (toBase L)
    (fieldMap K p s g hg L i) (fieldMap_over K p s g hg L i) hnc

variable (f : P ⟶ T) (a : Spec (.of L) ⟶ P)

/-- The changed original field fibre is a curve by the actual source iso. -/
theorem changedField_isCurve [IsCurve L (pullback.snd p (a ≫ f))] :
    IsCurve L (pullback.snd (pullback.snd p f) a) :=
  CurveTargetIsoDegree.isCurve _ _
    (ParameterFamilyCartesianComparison.testIso p f a)
    (ParameterFamilyCartesianComparison.testIso_hom_snd p f a)

attribute [local instance] changedField_isCurve

/-- Genus of the actual original fibre is unchanged, with no asserted
fibre-model or genus comparison premise. -/
theorem fieldGenus_change [IsProper (pullback.snd p (a ≫ f))] :
    genus (pullback.snd (pullback.snd p f) a) = genus (pullback.snd p (a ≫ f)) :=
  CurveSourceIsoDegree.genus_eq _ _
    (ParameterFamilyCartesianComparison.testIso p f a)
    (ParameterFamilyCartesianComparison.testIso_hom_snd p f a)

/-- The true native function-field degree on every changed field fibre
equals the original degree at the actual composite point. -/
theorem fieldDegree_change [IsCurve L (pullback.snd p (a ≫ f))]
    (hnc : ¬ ∃ y : Line L, ∀ c : (pullback p (a ≫ f) : Scheme.{u}),
      (fieldMap K p s g hg L (a ≫ f)).base c = y) :
    fieldDegree K L (pullback.snd p f) (f ≫ s) (changedLineMap K p g f)
      (changedLineMap_over K p s g hg f) a
      (fieldMap_change_nonconstant K p s g hg L f a hnc) =
        fieldDegree K L p s g hg (a ≫ f) hnc := by
  have : LocallyOfFiniteType (fieldMap K p s g hg L (a ≫ f)) :=
    locallyOfFiniteType_of_isCurve_comp L (pullback.snd p (a ≫ f))
      (toBase L) _ (fieldMap_over K p s g hg L (a ≫ f))
  have : IsDominant (fieldMap K p s g hg L (a ≫ f)) :=
    isDominant_of_not_constant L (pullback.snd p (a ≫ f)) (toBase L) _ hnc
  have : LocallyOfFiniteType
      (fieldMap K (pullback.snd p f) (f ≫ s) (changedLineMap K p g f)
        (changedLineMap_over K p s g hg f) L a) :=
    locallyOfFiniteType_of_isCurve_comp L (pullback.snd (pullback.snd p f) a)
      (toBase L) _ (fieldMap_over _ _ _ _ _ _ _)
  have : IsDominant
      (fieldMap K (pullback.snd p f) (f ≫ s) (changedLineMap K p g f)
        (changedLineMap_over K p s g hg f) L a) :=
    isDominant_of_not_constant L (pullback.snd (pullback.snd p f) a) (toBase L) _
      (fieldMap_change_nonconstant K p s g hg L f a hnc)
  change degreeOver _ = degreeOver _
  have hd := CurveSourceIsoDegree.degreeOver_precomp_iso
    (ParameterFamilyCartesianComparison.testIso p f a) (fieldMap K p s g hg L (a ≫ f))
  simpa only [← fieldMap_change K p s g hg L f a] using hd

end M9Native.ConstantP1CoverDegreeBaseChange

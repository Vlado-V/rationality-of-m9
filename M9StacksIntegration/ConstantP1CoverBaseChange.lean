module

public import M9StacksIntegration.CurveSourceIsoDegree
public import M9StacksIntegration.ParameterFamilyCartesianComparison
public import M9StacksIntegration.ConstantProjectiveLineFibre

/-!
# The actual constant-P1 cover after parameter base change

Every field map is constructed by the original projective-space
pullback square. Pullback pasting proves its compatibility with an
arbitrary change of parameters, including nonreduced parameters.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.ConstantP1CoverBaseChange

open PencilProjectiveLineGeometry

variable (K : Type u) [Field K] {X T P : Scheme.{u}}
  (p : X ⟶ T) (s : T ⟶ Spec (.of K))
  (g : X ⟶ Line K) (hg : g ≫ toBase K = p ≫ s)

/-- The genuine map to the original constant family, retaining its parameter. -/
def familyMap : X ⟶ ConstantProjectiveLineFibre.target K s :=
  pullback.lift g p hg

/-- The actual map is over the original family projection. -/
theorem familyMap_over :
    familyMap K p s g hg ≫ ConstantProjectiveLineFibre.projection K s = p :=
  pullback.lift_snd _ _ _

/-- The actual map to the original projective line is unchanged. -/
theorem familyMap_toLine :
    familyMap K p s g hg ≫ pullback.fst (toBase K) s = g :=
  pullback.lift_fst _ _ _

variable (L : Type u) [Field L] (i : Spec (.of L) ⟶ T)

include hg in
/-- The compatibility square for the original field-fibre map. -/
theorem fieldSquare :
    (pullback.fst p i ≫ g) ≫ toBase K = pullback.snd p i ≫ (i ≫ s) := by
  rw [Category.assoc, hg, ← Category.assoc, pullback.condition, Category.assoc]

/-- The literal native projective line over the actual test field is
obtained from its genuine projective-space base-change square. -/
def fieldMap : pullback p i ⟶ Line L :=
  (isPullback_projectiveSpaceOverMap 1 (i ≫ s)).lift
    (pullback.fst p i ≫ g) (pullback.snd p i) (fieldSquare K p s g hg L i)

/-- The original field-fibre structure map is retained. -/
theorem fieldMap_over : fieldMap K p s g hg L i ≫ toBase L = pullback.snd p i :=
  IsPullback.lift_snd _ _ _ _

/-- The original map to the initial projective line is retained. -/
theorem fieldMap_toOriginal :
    fieldMap K p s g hg L i ≫ projectiveSpaceOverMap 1 (i ≫ s) =
      pullback.fst p i ≫ g :=
  IsPullback.lift_fst _ _ _ _

variable (f : P ⟶ T)

/-- The actual map on the changed total family, before any field fibre. -/
def changedLineMap : pullback p f ⟶ Line K := pullback.fst p f ≫ g

include hg in
/-- The changed map retains the new original parameter structure. -/
theorem changedLineMap_over :
    changedLineMap K p g f ≫ toBase K = pullback.snd p f ≫ (f ≫ s) := by
  rw [changedLineMap, Category.assoc, hg, ← Category.assoc,
    pullback.condition, Category.assoc]

/-- The changed cover is an actual map to the new constant target. -/
def changedFamilyMap :
    pullback p f ⟶ ConstantProjectiveLineFibre.target K (f ≫ s) :=
  familyMap K (pullback.snd p f) (f ≫ s) (changedLineMap K p g f)
    (changedLineMap_over K p s g hg f)

/-- It is over the changed family's original parameter projection. -/
theorem changedFamilyMap_over :
    changedFamilyMap K p s g hg f ≫
      ConstantProjectiveLineFibre.projection K (f ≫ s) = pullback.snd p f :=
  familyMap_over _ _ _ _ _

/-- On every actual field-valued parameter point, the changed cover is
the original field cover precomposed with the genuine source-fibre iso. -/
theorem fieldMap_change (a : Spec (.of L) ⟶ P) :
    fieldMap K (pullback.snd p f) (f ≫ s) (changedLineMap K p g f)
      (changedLineMap_over K p s g hg f) L a =
        (ParameterFamilyCartesianComparison.testIso p f a).hom ≫
          fieldMap K p s g hg L (a ≫ f) := by
  apply (isPullback_projectiveSpaceOverMap 1 (a ≫ f ≫ s)).hom_ext
  · have hr := fieldMap_toOriginal K p s g hg L (a ≫ f)
    simp only [Category.assoc] at hr
    rw [fieldMap_toOriginal, Category.assoc, hr]
    rw [← Category.assoc, ParameterFamilyCartesianComparison.testIso_hom_fst]
    rw [changedLineMap, Category.assoc]
  · change fieldMap K (pullback.snd p f) (f ≫ s) (changedLineMap K p g f)
      (changedLineMap_over K p s g hg f) L a ≫ toBase L =
        ((ParameterFamilyCartesianComparison.testIso p f a).hom ≫
          fieldMap K p s g hg L (a ≫ f)) ≫ toBase L
    rw [fieldMap_over, Category.assoc, fieldMap_over,
      ParameterFamilyCartesianComparison.testIso_hom_snd]

include hg in
/-- Actual nonconstancy is preserved for every field point after the
specified parameter change, without a field-fibre identification premise. -/
theorem fieldMap_change_nonconstant (a : Spec (.of L) ⟶ P)
    (hnc : ¬ ∃ y : Line L, ∀ c : (pullback p (a ≫ f) : Scheme.{u}),
      (fieldMap K p s g hg L (a ≫ f)).base c = y) :
    ¬ ∃ y : Line L, ∀ c : (pullback (pullback.snd p f) a : Scheme.{u}),
      (fieldMap K (pullback.snd p f) (f ≫ s) (changedLineMap K p g f)
        (changedLineMap_over K p s g hg f) L a).base c = y := by
  rw [fieldMap_change K p s g hg L f a]
  exact CurveSourceIsoDegree.nonconstant_precomp
    (ParameterFamilyCartesianComparison.testIso p f a) _ hnc

end M9Native.ConstantP1CoverBaseChange

module

public import M9StacksIntegration.ConstantP1CoverDegreeBaseChange
public import M9StacksIntegration.ParameterP1SourceImage

/-!
# The actual field-cover construction matches the original H1 endpoint

The comparison is obtained from the two original projective-space
projection laws. Consequently the genuine native degree on field
fibres is the same degree used by the checked parameter-H1 obstruction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] isCurve_projectiveSpaceOver_one

universe u

namespace M9Native.ConstantP1CoverPointCoordinates

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange

variable (K : Type u) [Field K] {X T : Scheme.{u}}
  (p : X ⟶ T) [Flat p] (s : T ⟶ Spec (.of K))
  (g : X ⟶ Line K) (hg : g ≫ toBase K = p ≫ s) (x : T)

local notation "κ" => IsLocalRing.ResidueField (T.presheaf.stalk x)

omit [Flat p] in
/-- Both constructions give the SAME actual morphism to native P1 over
the original residue field; the projective-space pullback proves equality. -/
theorem fieldMap_eq_pointMap :
    fieldMap K p s g hg κ (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x) =
      ParameterP1SourceImage.pointMap K s p (familyMap K p s g hg)
        (familyMap_over K p s g hg) x := by
  apply (isPullback_projectiveSpaceOverMap 1 (T.fromSpecResidueField x ≫ s)).hom_ext
  · rw [fieldMap_toOriginal, ParameterP1SourceImage.pointMap_toOriginal,
      familyMap_toLine]
  · change fieldMap K p s g hg κ (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x) ≫ toBase κ =
      ParameterP1SourceImage.pointMap K s p (familyMap K p s g hg)
        (familyMap_over K p s g hg) x ≫ toBase κ
    rw [fieldMap_over, ParameterP1SourceImage.pointMap_over]
    rfl

omit [Flat p] in
/-- Actual nonconstancy on the normalized native field line implies
nonconstancy of the original pulled constant-family target map. -/
theorem originalPointMap_nonconstant
    (hnc : ¬ ∃ y : Line κ, ∀ c : (pullback p (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x) : Scheme.{u}),
      (fieldMap K p s g hg κ (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x)).base c = y) :
    ¬ ∃ y : (ParameterTangentDeformation.fibre
        (ConstantProjectiveLineFibre.projection K s) x).left,
      ∀ c : (ParameterTangentDeformation.fibre p x).left,
        (ParameterP1SourceImage.originalPointMap K s p (familyMap K p s g hg)
          (familyMap_over K p s g hg) x).base c = y := by
  rintro ⟨y, hy⟩
  apply hnc
  refine ⟨(ParameterP1SourceImage.pointTargetIso K s x).hom y, fun c => ?_⟩
  rw [fieldMap_eq_pointMap K p s g hg x]
  change (ParameterP1SourceImage.pointTargetIso K s x).hom
      ((ParameterP1SourceImage.originalPointMap K s p (familyMap K p s g hg)
        (familyMap_over K p s g hg) x) c) = _
  exact congrArg (ParameterP1SourceImage.pointTargetIso K s x).hom (hy c)

variable [IsCurve (IsLocalRing.ResidueField (T.presheaf.stalk x))
  (ParameterTangentDeformation.fibre p x).hom]

local instance sourceFieldCurve :
    IsCurve κ (pullback.snd p
      (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x)) :=
  inferInstanceAs (IsCurve κ (ParameterTangentDeformation.fibre p x).hom)

omit [Flat p] in
/-- The original native degree used by the H1 image bound is derived
from the actual field cover, with no assumed field or degree comparison. -/
theorem pointDegree_eq_fieldDegree
    (hnc : ¬ ∃ y : Line κ, ∀ c : (pullback p (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x) : Scheme.{u}),
      (fieldMap K p s g hg κ (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x)).base c = y) :
    ParameterP1SourceImage.pointDegree K s p (familyMap K p s g hg)
      (familyMap_over K p s g hg) x (originalPointMap_nonconstant K p s g hg x hnc) =
        ConstantP1CoverDegreeBaseChange.fieldDegree K κ p s g hg
          (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x) hnc := by
  have hd := ParameterP1SourceImage.pointDegree_eq_native K s p (familyMap K p s g hg)
    (familyMap_over K p s g hg) x (originalPointMap_nonconstant K p s g hg x hnc)
  have : LocallyOfFiniteType (fieldMap K p s g hg κ
      (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x)) :=
    locallyOfFiniteType_of_isCurve_comp κ
      (pullback.snd p (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x))
      (toBase κ) _ (fieldMap_over _ _ _ _ _ _ _)
  have : IsDominant (fieldMap K p s g hg κ
      (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x)) :=
    isDominant_of_not_constant κ
      (pullback.snd p (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x))
      (toBase κ) _ hnc
  have : LocallyOfFiniteType (ParameterP1SourceImage.pointMap K s p
      (familyMap K p s g hg) (familyMap_over K p s g hg) x) :=
    locallyOfFiniteType_of_isCurve_comp κ (ParameterTangentDeformation.fibre p x).hom
      (toBase κ) _ (ParameterP1SourceImage.pointMap_over _ _ _ _ _ _)
  have : IsDominant (ParameterP1SourceImage.pointMap K s p
      (familyMap K p s g hg) (familyMap_over K p s g hg) x) :=
    isDominant_of_not_constant κ (ParameterTangentDeformation.fibre p x).hom (toBase κ) _
      (CurveTargetIsoDegree.nonconstant_comp (ParameterP1SourceImage.pointTargetIso K s x)
        _ (originalPointMap_nonconstant K p s g hg x hnc))
  rw [hd]
  change degreeOver (ParameterP1SourceImage.pointMap K s p (familyMap K p s g hg)
    (familyMap_over K p s g hg) x) =
      degreeOver (fieldMap K p s g hg κ
        (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x))
  simp only [fieldMap_eq_pointMap K p s g hg x]

end M9Native.ConstantP1CoverPointCoordinates

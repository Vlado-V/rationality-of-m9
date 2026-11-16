module

public import M9StacksIntegration.ParameterMorphismTangent
public import M9StacksIntegration.SchemeMorphismTargetMarking
public import M9StacksIntegration.ConstantProjectiveLineFibre
public import M9StacksIntegration.CurveTargetIsoDegree
public import M9StacksIntegration.ParameterClosedResidueField
public import M9StacksIntegration.SchemeMorphismP1SourceImage

/-!
# Actual P¹ cover-family tangent image at original parameter points

The target is the actual constant family. Its original field fibre is
identified with the literal native P¹ by the proved projective-space
base-change square. Changing only its target marking preserves the
actual source deformation. The degree comparison is the original native
function-field degree comparison under that genuine isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 1024

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] isCurve_projectiveSpaceOver_one
attribute [local instance] M9Native.ParameterTangentH1.residueTangentModule

universe u

namespace M9Native.ParameterP1SourceImage

open PencilProjectiveLineGeometry ParameterTangentDeformation

variable (K : Type u) [Field K] {X T : Scheme.{u}}
  (s : T ⟶ Spec (.of K)) (p : X ⟶ T) [Flat p]

local instance targetProjection_flat : Flat (ConstantProjectiveLineFibre.projection K s) := by
  have : Smooth (toBase K) := CurveP1NormalSections.line_smooth K
  change Flat (pullback.snd (toBase K) s)
  infer_instance

/-- The genuine target-fibre comparison, constructed without a target-model premise. -/
def pointTargetIso (x : T) :
    (fibre (ConstantProjectiveLineFibre.projection K s) x).left ≅
      Line (IsLocalRing.ResidueField (T.presheaf.stalk x)) :=
  ConstantProjectiveLineFibre.fibreIso K
    (IsLocalRing.ResidueField (T.presheaf.stalk x)) s (T.fromSpecResidueField x)

/-- The actual target marking preserves the original field structural map. -/
theorem pointTargetIso_over (x : T) :
    (pointTargetIso K s x).hom ≫ toBase (IsLocalRing.ResidueField (T.presheaf.stalk x)) =
      (fibre (ConstantProjectiveLineFibre.projection K s) x).hom :=
  ConstantProjectiveLineFibre.fibreIso_over K _ s (T.fromSpecResidueField x)

local instance pointTarget_curve (x : T) :
    IsCurve (IsLocalRing.ResidueField (T.presheaf.stalk x))
      (fibre (ConstantProjectiveLineFibre.projection K s) x).hom :=
  CurveTargetIsoDegree.isCurve _ _ (pointTargetIso K s x) (pointTargetIso_over K s x)

variable (h : X ⟶ ConstantProjectiveLineFibre.target K s)
  (hh : h ≫ ConstantProjectiveLineFibre.projection K s = p) (x : T)

local notation "κ" => IsLocalRing.ResidueField (T.presheaf.stalk x)

/-- The actual map between the original residue-field fibres of the family. -/
abbrev originalPointMap := ParameterMorphismTangent.fibreMap p
  (ConstantProjectiveLineFibre.projection K s) h hh x

omit [Flat p] in
/-- Its original actual field-base triangle. -/
theorem originalPointMap_over :
    originalPointMap K s p h hh x ≫
      (fibre (ConstantProjectiveLineFibre.projection K s) x).hom = (fibre p x).hom :=
  ParameterMorphismTangent.fibreMap_over p
    (ConstantProjectiveLineFibre.projection K s) h hh x

/-- The actual field cover to the literal native P¹ after its derived target comparison. -/
def pointMap : (fibre p x).left ⟶ Line κ :=
  originalPointMap K s p h hh x ≫ (pointTargetIso K s x).hom

omit [Flat p] in
/-- The actual field-cover triangle, rather than an assumed base comparison. -/
theorem pointMap_over : pointMap K s p h hh x ≫ toBase κ = (fibre p x).hom :=
  SchemeMorphismTargetMarking.retarget_over _ _ _ _
    (originalPointMap_over K s p h hh x) (pointTargetIso K s x)
    (pointTargetIso_over K s x)

omit [Flat p] in
/-- The literal native field cover is the original family morphism after
the genuine projective-space base change, with no map-identification premise. -/
theorem pointMap_toOriginal :
    pointMap K s p h hh x ≫ projectiveSpaceOverMap 1 (T.fromSpecResidueField x ≫ s) =
      pullback.fst p (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x) ≫ h ≫
        pullback.fst (toBase K) s := by
  rw [pointMap, Category.assoc]
  have hc := ConstantProjectiveLineFibre.fibreIso_toOriginal K κ s
    (T.fromSpecResidueField x)
  rw [show (pointTargetIso K s x).hom ≫
      projectiveSpaceOverMap 1 (T.fromSpecResidueField x ≫ s) =
        pullback.fst (ConstantProjectiveLineFibre.projection K s)
          (show Spec (.of κ) ⟶ T from T.fromSpecResidueField x) ≫
            pullback.fst (toBase K) s from hc]
  rw [← Category.assoc]
  exact congrArg (fun a => a ≫ pullback.fst (toBase K) s)
    (ParameterMorphismDeformation.pulledMap_toFamily (Z := Spec (.of κ)) p
      (ConstantProjectiveLineFibre.projection K s) h hh (T.fromSpecResidueField x))

variable [IsCurve (IsLocalRing.ResidueField (T.presheaf.stalk x)) (fibre p x).hom]

/-- The original degree on the actual pulled target is the native function-field degree. -/
def pointDegree
    (hnc : ¬ ∃ y : (fibre (ConstantProjectiveLineFibre.projection K s) x).left,
      ∀ c : (fibre p x).left, (originalPointMap K s p h hh x).base c = y) : ℕ :=
  PencilDegreePullback.curveMapDegree (fibre p x).hom
    (fibre (ConstantProjectiveLineFibre.projection K s) x).hom
    (originalPointMap K s p h hh x) (originalPointMap_over K s p h hh x) hnc

omit [Flat p] in
/-- Genuine target-isomorphism invariance identifies both actual native field degrees. -/
theorem pointDegree_eq_native
    (hnc : ¬ ∃ y : (fibre (ConstantProjectiveLineFibre.projection K s) x).left,
      ∀ c : (fibre p x).left, (originalPointMap K s p h hh x).base c = y) :
    pointDegree K s p h hh x hnc =
      PencilDegreePullback.curveMapDegree (fibre p x).hom (toBase κ)
        (pointMap K s p h hh x) (pointMap_over K s p h hh x)
        (CurveTargetIsoDegree.nonconstant_comp (pointTargetIso K s x)
          (originalPointMap K s p h hh x) hnc) :=
  (CurveTargetIsoDegree.curveMapDegree_comp_iso _ _ (pointTargetIso K s x)
    (pointTargetIso_over K s x) (fibre p x).hom
    (originalPointMap K s p h hh x) (originalPointMap_over K s p h hh x) hnc).symm

variable [Smooth (fibre p x).hom] [IsProper (fibre p x).hom]

/-- Same original parameter-H¹ image, bounded through a genuinely retargeted
native morphism deformation and the actual genus-nine P¹ source-image theorem. -/
theorem tangentH1_finrank_le_twenty_three_of_residue
    [IsAlgClosed κ] [CharZero κ] (hg : genus (fibre p x).hom = 9)
    (hnc : ¬ ∃ y : (fibre (ConstantProjectiveLineFibre.projection K s) x).left,
      ∀ c : (fibre p x).left, (originalPointMap K s p h hh x).base c = y)
    (hd : pointDegree K s p h hh x hnc ≤ 5) :
    Module.finrank κ (LinearMap.range (ParameterTangentH1.tangentH1LinearMap p s x)) ≤ 23 := by
  have : Module.Finite κ (cohomologyOverField κ (fibre p x).hom
      (CurveTangentLineGeometry.tangentLine (fibre p x).hom) 1) :=
    Module.finite_of_finrank_pos (by
      rw [SmoothCurveTangentCohomology.tangent_h1 (fibre p x).hom hg]
      decide)
  have h₀ := ParameterMorphismTangent.tangentH1_range_le_actual_sourceForgettingH1 p
    (ConstantProjectiveLineFibre.projection K s) h hh s x
  have h₁ := SchemeMorphismTargetMarking.sourceH1_range_le (fibre p x).hom
    (fibre (ConstantProjectiveLineFibre.projection K s) x).hom (toBase κ)
    (originalPointMap K s p h hh x) (originalPointMap_over K s p h hh x)
    (pointTargetIso K s x) (pointTargetIso_over K s x)
  have hdegree : PencilDegreePullback.curveMapDegree (fibre p x).hom (toBase κ)
      (pointMap K s p h hh x) (pointMap_over K s p h hh x)
      (CurveTargetIsoDegree.nonconstant_comp (pointTargetIso K s x)
        (originalPointMap K s p h hh x) hnc) ≤ 5 := by
    rw [← pointDegree_eq_native K s p h hh x hnc]
    exact hd
  exact (Submodule.finrank_mono (h₀.trans h₁)).trans
    (SchemeMorphismP1SourceImage.sourceForgettingH1_finrank_le_twenty_three
      (fibre p x).hom (pointMap K s p h hh x) (pointMap_over K s p h hh x) hg
      (CurveTargetIsoDegree.nonconstant_comp (pointTargetIso K s x)
        (originalPointMap K s p h hh x) hnc) hdegree)

/-- At actual closed parameter points over the original AC char-zero base,
the residue-field properties are derived. No target isomorphism or image
bound is supplied to this actual constant-cover-family endpoint. -/
theorem tangentH1_finrank_le_twenty_three [IsAlgClosed K] [CharZero K]
    [LocallyOfFiniteType s] (hx : IsClosed ({x} : Set T))
    (hg : genus (fibre p x).hom = 9)
    (hnc : ¬ ∃ y : (fibre (ConstantProjectiveLineFibre.projection K s) x).left,
      ∀ c : (fibre p x).left, (originalPointMap K s p h hh x).base c = y)
    (hd : pointDegree K s p h hh x hnc ≤ 5) :
    Module.finrank κ (LinearMap.range (ParameterTangentH1.tangentH1LinearMap p s x)) ≤ 23 := by
  have : IsAlgClosed κ := ParameterClosedResidueField.isAlgClosed K s x hx
  have : CharZero κ := ParameterClosedResidueField.charZero K s x hx
  exact tangentH1_finrank_le_twenty_three_of_residue K s p h hh x hg hnc hd

end M9Native.ParameterP1SourceImage

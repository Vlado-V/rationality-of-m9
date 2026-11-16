module

public import M9StacksIntegration.CurveFieldFamilyArrow
public import M9StacksIntegration.CurveClassifierPullback

/-!
# Actual marked pullbacks of the ground-field Curves classifier

The point, test and special arrows are obtained from the original scheme
pullback and lifted to the genuine field base change. The canonical
cartesian comparisons retain the marked special-fibre arrow.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin
open Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u
namespace M9Native.CurveFieldClassifierPullback

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K))

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p

abbrev originalFamily := CurveClassifierPullback.originalFamily B hZ hX hT p
abbrev base := CurveFieldClassifyingFamily.fieldBase B hZ hK
  (originalFamily B hZ hX hT p) s
abbrev family := CurveFieldClassifyingFamily.fieldFamily B hZ hK hAlg
  (originalFamily B hZ hX hT p) s
abbrev classifier := CurveFieldClassifyingFamily.classifyingMor B hZ hK hAlg
  (originalFamily B hZ hX hT p) s

variable {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  (i : Spec (.of k) ⟶ T)
  [IsCurve k (ParameterFamilyDeformation.fibre p i).hom]

local instance fibreProper : IsProper (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (IsProper (pullback.snd p i))
local instance fibreSmooth : Smooth (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (Smooth (pullback.snd p i))

/-- The coefficient-field identity is the actual identity spectrum map. -/
theorem spec_identity : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
  change Spec.map (𝟙 (.of k)) = _
  exact Spec.map_id _

/-- The original coefficient point retains its literal map to the ground field. -/
abbrev pointStructure := Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ (i ≫ s)

abbrev pointFamily := CurveFieldClassifyingFamily.fieldFamily B hZ hK hAlg
  (CurveClassifierPullback.pointFamily B hZ p hk i) (pointStructure s i)

omit [SmoothOfRelativeDimension 1 p] in
/-- This is exactly the field point used by the genuine target comparison. -/
theorem pointFamily_eq_fieldPoint : pointFamily B hZ hK hAlg p s hk i =
    CurveFieldTargetComparison.fieldPoint B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom := rfl

/-- The original point projection respects the actual ground structure. -/
theorem point_ground :
    B.inclusion.map (CurveClassifierPullback.pointProjection B hZ hX hT p hk i).baseMap.left ≫
        s = pointStructure s i := by
  change i ≫ s = _
  rw [pointStructure, spec_identity]
  exact (Category.id_comp _).symm

abbrev pointBase := CurveFieldFamilyArrow.baseArrow B hZ hK
  (Q := (CurveClassifierPullback.pointFamily B hZ p hk i)) (R := (originalFamily B hZ hX hT p)) (pointStructure s i) s
  (CurveClassifierPullback.pointProjection B hZ hX hT p hk i)
  (point_ground B hZ hX hT p s hk i)

abbrev pointProjection := CurveFieldFamilyArrow.arrow B hZ hK hAlg
  (Q := (CurveClassifierPullback.pointFamily B hZ p hk i)) (R := (originalFamily B hZ hX hT p)) (pointStructure s i) s
  (CurveClassifierPullback.pointProjection B hZ hX hT p hk i)
  (point_ground B hZ hX hT p s hk i)

abbrev parameterPoint : Over (base B hZ hK hX hT p s) :=
  Over.mk (pointBase B hZ hK hX hT p s hk i)

local instance fieldFibered :
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsFibered :=
  (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.property.isFibered

/-- The point arrow is genuinely cartesian over the original point map. -/
theorem pointProjection_cartesian :
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (pointBase B hZ hK hX hT p s hk i) (pointProjection B hZ hK hAlg hX hT p s hk i) :=
  CurveFieldFamilyArrow.arrow_isStronglyCartesian B hZ hK hAlg
  (Q := (CurveClassifierPullback.pointFamily B hZ p hk i)) (R := (originalFamily B hZ hX hT p)) (pointStructure s i) s
    (CurveClassifierPullback.pointProjection B hZ hX hT p hk i)
    (point_ground B hZ hX hT p s hk i)

/-- Its actual classifier value is the original marked fibre. -/
def pointValueIso : (classifier B hZ hK hAlg hX hT p s).toFunctor.obj
    (parameterPoint B hZ hK hX hT p s hk i) ≅ pointFamily B hZ hK hAlg p s hk i := by
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (parameterPoint B hZ hK hX hT p s hk i).hom
      (pointProjection B hZ hK hAlg hX hT p s hk i) := by
    change (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (pointBase B hZ hK hX hT p s hk i) _
    exact pointProjection_cartesian B hZ hK hAlg hX hT p s hk i
  exact FiberedClassifierCartesianValue.valueIso
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (base B hZ hK hX hT p s)
    (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK hAlg
      (originalFamily B hZ hX hT p) s)
    (parameterPoint B hZ hK hX hT p s hk i)
    (pointProjection B hZ hK hAlg hX hT p s hk i)

variable (A : ArtinianLocalAlgCat.{u,u,u} k k)
  (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i)
  (haS : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ (i ≫ s))

abbrev testStructure := Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ (i ≫ s)
abbrev testFamily := CurveFieldClassifyingFamily.fieldFamily B hZ hK hAlg
  (CurveClassifierPullback.testFamily B hZ p hk i A a ha) (testStructure s i A)

include haS in
/-- The original test projection is over the specified original field base. -/
theorem test_ground :
    B.inclusion.map (CurveClassifierPullback.testProjection B hZ hX hT p hk i A a ha).baseMap.left ≫
        s = testStructure s i A := haS

abbrev testBase := CurveFieldFamilyArrow.baseArrow B hZ hK
  (Q := (CurveClassifierPullback.testFamily B hZ p hk i A a ha)) (R := (originalFamily B hZ hX hT p)) (testStructure s i A) s
  (CurveClassifierPullback.testProjection B hZ hX hT p hk i A a ha)
  (test_ground B hZ hX hT p s hk i A a ha haS)

abbrev testProjection := CurveFieldFamilyArrow.arrow B hZ hK hAlg
  (Q := (CurveClassifierPullback.testFamily B hZ p hk i A a ha)) (R := (originalFamily B hZ hX hT p)) (testStructure s i A) s
  (CurveClassifierPullback.testProjection B hZ hX hT p hk i A a ha)
  (test_ground B hZ hX hT p s hk i A a ha haS)

/-- The actual test arrow is cartesian in the original field-based stack. -/
theorem testProjection_cartesian :
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (testBase B hZ hK hX hT p s hk i A a ha haS)
      (testProjection B hZ hK hAlg hX hT p s hk i A a ha haS) :=
  CurveFieldFamilyArrow.arrow_isStronglyCartesian B hZ hK hAlg
  (Q := (CurveClassifierPullback.testFamily B hZ p hk i A a ha)) (R := (originalFamily B hZ hX hT p)) (testStructure s i A) s
    (CurveClassifierPullback.testProjection B hZ hX hT p hk i A a ha)
    (test_ground B hZ hX hT p s hk i A a ha haS)

/-- The actual field classifier test is isomorphic to the original pulled test family. -/
def testValueIso : (classifier B hZ hK hAlg hX hT p s).toFunctor.obj
    (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)) ≅
      testFamily B hZ hK hAlg p s hk i A a ha := by
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)).hom
      (testProjection B hZ hK hAlg hX hT p s hk i A a ha haS) := by
    change (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (testBase B hZ hK hX hT p s hk i A a ha haS) _
    exact testProjection_cartesian B hZ hK hAlg hX hT p s hk i A a ha haS
  exact FiberedClassifierCartesianValue.valueIso
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (base B hZ hK hX hT p s)
    (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK hAlg
      (originalFamily B hZ hX hT p) s)
    (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS))
    (testProjection B hZ hK hAlg hX hT p s hk i A a ha haS)

/-- The original special arrow is over the exact residue/ground square. -/
theorem special_ground :
    B.inclusion.map (CurveClassifierPullback.specialArrow B hZ p hk i
      (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) A a ha).baseMap.left ≫
        testStructure s i A = pointStructure s i := by
  change residueSpecMap A ≫ (Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ (i ≫ s)) = _
  rw [← Category.assoc, spec_map_residueMap_comp_spec_map_algebraMap]

abbrev specialBase := CurveFieldFamilyArrow.baseArrow B hZ hK
  (Q := (CurveClassifierPullback.pointFamily B hZ p hk i)) (R := (CurveClassifierPullback.testFamily B hZ p hk i A a ha)) (pointStructure s i)
  (testStructure s i A) (CurveClassifierPullback.specialArrow B hZ p hk i
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) A a ha)
  (special_ground B hZ p s hk i A a ha)

abbrev specialArrow := CurveFieldFamilyArrow.arrow B hZ hK hAlg
  (Q := (CurveClassifierPullback.pointFamily B hZ p hk i)) (R := (CurveClassifierPullback.testFamily B hZ p hk i A a ha)) (pointStructure s i)
  (testStructure s i A) (CurveClassifierPullback.specialArrow B hZ p hk i
    (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) A a ha)
  (special_ground B hZ p s hk i A a ha)

/-- The actual lifted special arrow retains the original projection triangle. -/
theorem specialArrow_projection :
    specialArrow B hZ hK hAlg p s hk i A a ha ≫
        testProjection B hZ hK hAlg hX hT p s hk i A a ha haS =
      pointProjection B hZ hK hAlg hX hT p s hk i := by
  apply (CurveFieldClassifyingFamily.smallProjection B hZ hK hAlg).map_injective
  rw [Functor.map_comp]
  change (CurveFieldClassifyingFamily.smallProjection B hZ hK hAlg).map
      (CurveFieldFamilyArrow.arrow _ _ _ _ _ _ _ _) ≫
      (CurveFieldClassifyingFamily.smallProjection B hZ hK hAlg).map
        (CurveFieldFamilyArrow.arrow _ _ _ _ _ _ _ _) =
      (CurveFieldClassifyingFamily.smallProjection B hZ hK hAlg).map
        (CurveFieldFamilyArrow.arrow _ _ _ _ _ _ _ _)
  rw [CurveFieldFamilyArrow.arrow_smallProjection, CurveFieldFamilyArrow.arrow_smallProjection,
    CurveFieldFamilyArrow.arrow_smallProjection, ← Functor.map_comp,
    CurveClassifierPullback.specialArrow_projection]

/-- The original residue arrow between the two actual represented tests. -/
def specialBaseArrow : parameterPoint B hZ hK hX hT p s hk i ⟶
    Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS) :=
  Over.homMk (specialBase B hZ hK p s hk i A a ha) (by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact ha)

/-- The field classifier comparison preserves the ORIGINAL special-fibre arrow. -/
theorem testValueIso_marked :
    (pointValueIso B hZ hK hAlg hX hT p s hk i).inv ≫
        (classifier B hZ hK hAlg hX hT p s).toFunctor.map
          (specialBaseArrow B hZ hK hX hT p s hk i A a ha haS) ≫
        (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS).hom =
      specialArrow B hZ hK hAlg p s hk i A a ha := by
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (parameterPoint B hZ hK hX hT p s hk i).hom
      (pointProjection B hZ hK hAlg hX hT p s hk i) := by
    change (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (pointBase B hZ hK hX hT p s hk i) _
    exact pointProjection_cartesian B hZ hK hAlg hX hT p s hk i
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)).hom
      (testProjection B hZ hK hAlg hX hT p s hk i A a ha haS) := by
    change (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (testBase B hZ hK hX hT p s hk i A a ha haS) _
    exact testProjection_cartesian B hZ hK hAlg hX hT p s hk i A a ha haS
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsHomLift
      (specialBaseArrow B hZ hK hX hT p s hk i A a ha haS).left
      (specialArrow B hZ hK hAlg p s hk i A a ha) := by
    change (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsHomLift
      (specialBase B hZ hK p s hk i A a ha) _
    exact CurveFieldFamilyArrow.arrow_isHomLift B hZ hK hAlg
      (Q := (CurveClassifierPullback.pointFamily B hZ p hk i))
      (R := (CurveClassifierPullback.testFamily B hZ p hk i A a ha)) (pointStructure s i)
      (testStructure s i A) (CurveClassifierPullback.specialArrow B hZ p hk i
        (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) A a ha)
      (special_ground B hZ p s hk i A a ha)
  exact FiberedClassifierCartesianValue.valueIso_marked
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (base B hZ hK hX hT p s)
    (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK hAlg
      (originalFamily B hZ hX hT p) s)
    (specialBaseArrow B hZ hK hX hT p s hk i A a ha haS)
    (pointProjection B hZ hK hAlg hX hT p s hk i)
    (testProjection B hZ hK hAlg hX hT p s hk i A a ha haS)
    (specialArrow B hZ hK hAlg p s hk i A a ha)
    (specialArrow_projection B hZ hK hAlg hX hT p s hk i A a ha haS)

end M9Native.CurveFieldClassifierPullback

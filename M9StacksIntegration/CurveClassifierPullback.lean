module

public import M9StacksIntegration.FiberedClassifierCartesianValue
public import M9StacksIntegration.NativeSchematicCurveClassifier
public import M9StacksIntegration.ParameterFamilyDeformation
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison

/-!
# The native Curves classifier on an actual pulled scheme family

Every comparison here is derived from the original scheme pullback square.
The two-Yoneda classifier is the unchanged native classifier of the actual
family. The last identity retains the marked special fibre, as required for
a comparison of deformation classes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Artin Deformation.Examples

universe u

namespace M9Native.CurveClassifierPullback

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p

/-- The actual original bounded scheme-family map. -/
abbrev siteMap := integerSiteMap B hZ hX hT p

omit [IsProper p] [SmoothOfRelativeDimension 1 p] in
/-- The bounded presentation retains exactly the original scheme morphism. -/
theorem siteMap_toScheme :
    (BigFppfOver.toScheme B integerBase hZ).map (siteMap B hZ hX hT p) = p := rfl

local instance siteMapProper :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map (siteMap B hZ hX hT p)) := by
  rw [siteMap_toScheme]
  infer_instance

local instance siteMapSmooth :
    SmoothOfRelativeDimension 1
      ((BigFppfOver.toScheme B integerBase hZ).map (siteMap B hZ hX hT p)) := by
  rw [siteMap_toScheme]
  infer_instance

/-- The literal native family of this original proper smooth relative curve. -/
abbrev originalFamily :=
  M9StacksIntegration.NativeSchematicCurveFamily.properSmoothSchemeFamily B hZ
    (siteMap B hZ hX hT p) inferInstance inferInstance

/-- Its actual native two-Yoneda classifying morphism. -/
abbrev classifier :=
  M9StacksIntegration.NativeSchematicCurveClassifier.properSmoothClassifyingMor B hZ
    (siteMap B hZ hX hT p) inferInstance inferInstance

local instance originalCurveFibration : (curvesProjectionOver B hZ).IsFibered :=
  (curvesFiberedCategory B hZ).property.isFibered

local instance originalCurveCartesian {Y Z : CurveFamily B hZ} (f : Y ⟶ Z) :
    (curvesProjectionOver B hZ).IsStronglyCartesian f.baseMap f := by
  have : (curvesProjectionOver B hZ).IsHomLift f.baseMap f :=
    Functor.IsHomLift.map f
  have hp : (curvesProjectionOver B hZ).IsFiberedInGroupoids :=
    (curvesFiberedCategory B hZ).property
  exact hp.isStronglyCartesian_homLift f.baseMap f

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (hk : B.Contains (Spec (.of k))) (i : Spec (.of k) ⟶ T)
  [IsCurve k (ParameterFamilyDeformation.fibre p i).hom]

local instance fibreProper : IsProper (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (IsProper (pullback.snd p i))

omit [IsProper p] [SmoothOfRelativeDimension 1 p] in
/-- The original actual fibre has its genuine curve dimension. -/
theorem fibre_dimension : topologicalKrullDim (ParameterFamilyDeformation.fibre p i).left ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (f := (ParameterFamilyDeformation.fibre p i).hom)).le

/-- Its original native Curves point. -/
abbrev pointFamily :=
  curveFamilyOfScheme (ParameterFamilyDeformation.fibre p i) B hZ hk
    (fibre_dimension p i)

/-- The actual original fibre maps cartesianly to the original family. -/
def pointProjection : pointFamily B hZ p hk i ⟶ originalFamily B hZ hX hT p where
  baseMap := integerSiteMap B hZ hk hT i
  totalMap := schemeSpaceMap (integerSiteMap B hZ
    (contains_left_of_isProper B (X := ParameterFamilyDeformation.fibre p i) hk) hX
    (pullback.fst p i))
  cartesian := by
    change IsPullback
      (schemeSpaceMap (integerSiteMap B hZ _ hX (pullback.fst p i)))
      (schemeSpaceMap (integerSiteMap B hZ _ hk (pullback.snd p i)))
      (schemeSpaceMap (integerSiteMap B hZ hX hT p))
      (schemeSpaceMap (integerSiteMap B hZ hk hT i))
    exact isPullback_schemeSpaceMap_integerSiteMap (IsPullback.of_hasPullback p i)

/-- The exact original pulled deformation, on its original Artinian algebra. -/
abbrev testDeformation (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :=
  ParameterFamilyDeformation.deformation p i A a ha

/-- Its genuine native Curves family, retaining its literal total scheme. -/
abbrev testFamily (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :=
  (testDeformation p i A a ha).curveFamily B hZ hk (fibre_dimension p i)

/-- The original scheme pullback square constructs the actual Curves
morphism from the test family to the original family. -/
def testProjection (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    testFamily B hZ p hk i A a ha ⟶ originalFamily B hZ hX hT p where
  baseMap := integerSiteMap B hZ (contains_baseSpec B hk A) hT a
  totalMap := schemeSpaceMap (integerSiteMap B hZ
    ((testDeformation p i A a ha).contains_scheme B hk) hX (pullback.fst p a))
  cartesian := by
    change IsPullback
      (schemeSpaceMap (integerSiteMap B hZ _ hX (pullback.fst p a)))
      (schemeSpaceMap (integerSiteMap B hZ _ (contains_baseSpec B hk A) (pullback.snd p a)))
      (schemeSpaceMap (integerSiteMap B hZ hX hT p))
      (schemeSpaceMap (integerSiteMap B hZ (contains_baseSpec B hk A) hT a))
    exact isPullback_schemeSpaceMap_integerSiteMap (IsPullback.of_hasPullback p a)

variable (iΛ : Spec (.of Λ) ⟶ integerBase)

/-- The marked special-fibre arrow is exactly the original native 0DZU arrow. -/
abbrev specialArrow (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    pointFamily B hZ p hk i ⟶ testFamily B hZ p hk i A a ha :=
  ((testDeformation p i A a ha).toCurveDeformation B hZ hk
    (fibre_dimension p i) iΛ).arrow

/-- The actual special-fibre arrow commutes with the two projections to
the original family, including the literal original base map. -/
theorem specialArrow_projection (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    specialArrow B hZ p hk i iΛ A a ha ≫ testProjection B hZ hX hT p hk i A a ha =
      pointProjection B hZ hX hT p hk i := by
  apply CurveFamily.Hom.ext
  · change integerSiteMap B hZ hk (contains_baseSpec B hk A) (residueSpecMap A) ≫
      integerSiteMap B hZ (contains_baseSpec B hk A) hT a = integerSiteMap B hZ hk hT i
    rw [integerSiteMap_comp, ha]
  · change schemeSpaceMap (integerSiteMap B hZ _ _
        (testDeformation p i A a ha).specialMap) ≫
      schemeSpaceMap (integerSiteMap B hZ _ hX (pullback.fst p a)) =
      schemeSpaceMap (integerSiteMap B hZ _ hX (pullback.fst p i))
    rw [← schemeSpaceMap_comp, integerSiteMap_comp]
    exact congrArg (fun f => schemeSpaceMap (integerSiteMap B hZ
      (contains_left_of_isProper B (X := ParameterFamilyDeformation.fibre p i) hk) hX f))
      (ParameterFamilyDeformation.specialMap_toFamily p i A a ha)

/-- The classifier's value at the actual point is canonically the original fibre. -/
def pointValueIso :
    (classifier B hZ hX hT p).toFunctor.obj
        (Over.mk (pointProjection B hZ hX hT p hk i).baseMap) ≅
      pointFamily B hZ p hk i := by
  have : (curvesProjectionOver B hZ).IsStronglyCartesian
      (Over.mk (pointProjection B hZ hX hT p hk i).baseMap).hom
      (pointProjection B hZ hX hT p hk i) := by
    change (curvesProjectionOver B hZ).IsStronglyCartesian
      (pointProjection B hZ hX hT p hk i).baseMap (pointProjection B hZ hX hT p hk i)
    exact originalCurveCartesian B hZ _
  exact FiberedClassifierCartesianValue.valueIso (curvesProjectionOver B hZ)
    (integerSiteObject B hZ hT) rfl
    (Over.mk (pointProjection B hZ hX hT p hk i).baseMap)
    (pointProjection B hZ hX hT p hk i)

/-- The classifier's actual test value is canonically the literal pulled
family, by its genuine cartesian projection. -/
def testValueIso (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (classifier B hZ hX hT p).toFunctor.obj
        (Over.mk (testProjection B hZ hX hT p hk i A a ha).baseMap) ≅
      testFamily B hZ p hk i A a ha := by
  have : (curvesProjectionOver B hZ).IsStronglyCartesian
      (Over.mk (testProjection B hZ hX hT p hk i A a ha).baseMap).hom
      (testProjection B hZ hX hT p hk i A a ha) := by
    change (curvesProjectionOver B hZ).IsStronglyCartesian
      (testProjection B hZ hX hT p hk i A a ha).baseMap
      (testProjection B hZ hX hT p hk i A a ha)
    exact originalCurveCartesian B hZ _
  exact FiberedClassifierCartesianValue.valueIso (curvesProjectionOver B hZ)
    (integerSiteObject B hZ hT) rfl
    (Over.mk (testProjection B hZ hX hT p hk i A a ha).baseMap)
    (testProjection B hZ hX hT p hk i A a ha)

/-- The actual residue map as an arrow in the original represented source. -/
def specialBaseArrow (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    Over.mk (pointProjection B hZ hX hT p hk i).baseMap ⟶
      Over.mk (testProjection B hZ hX hT p hk i A a ha).baseMap :=
  Over.homMk (specialArrow B hZ p hk i iΛ A a ha).baseMap
    (congrArg CurveFamily.Hom.baseMap
      (specialArrow_projection B hZ hX hT p hk i iΛ A a ha))

/-- The classifier comparison preserves the ORIGINAL marked special-fibre
arrow; it is a comparison of pointed deformations, not just their totals. -/
theorem testValueIso_marked (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (pointValueIso B hZ hX hT p hk i).inv ≫
      (classifier B hZ hX hT p).toFunctor.map (specialBaseArrow B hZ hX hT p hk i iΛ A a ha) ≫
      (testValueIso B hZ hX hT p hk i A a ha).hom =
      specialArrow B hZ p hk i iΛ A a ha := by
  have : (curvesProjectionOver B hZ).IsStronglyCartesian
      (Over.mk (pointProjection B hZ hX hT p hk i).baseMap).hom
      (pointProjection B hZ hX hT p hk i) := by
    change (curvesProjectionOver B hZ).IsStronglyCartesian
      (pointProjection B hZ hX hT p hk i).baseMap (pointProjection B hZ hX hT p hk i)
    exact originalCurveCartesian B hZ _
  have : (curvesProjectionOver B hZ).IsStronglyCartesian
      (Over.mk (testProjection B hZ hX hT p hk i A a ha).baseMap).hom
      (testProjection B hZ hX hT p hk i A a ha) := by
    change (curvesProjectionOver B hZ).IsStronglyCartesian
      (testProjection B hZ hX hT p hk i A a ha).baseMap
      (testProjection B hZ hX hT p hk i A a ha)
    exact originalCurveCartesian B hZ _
  have : (curvesProjectionOver B hZ).IsHomLift
      (specialBaseArrow B hZ hX hT p hk i iΛ A a ha).left
      (specialArrow B hZ p hk i iΛ A a ha) := by
    change (curvesProjectionOver B hZ).IsHomLift
      (specialArrow B hZ p hk i iΛ A a ha).baseMap (specialArrow B hZ p hk i iΛ A a ha)
    exact Functor.IsHomLift.map (p := curvesProjectionOver B hZ)
      (specialArrow B hZ p hk i iΛ A a ha)
  have h := FiberedClassifierCartesianValue.valueIso_marked (curvesProjectionOver B hZ)
    (y := originalFamily B hZ hX hT p)
    (integerSiteObject B hZ hT) rfl
    (specialBaseArrow B hZ hX hT p hk i iΛ A a ha)
    (pointProjection B hZ hX hT p hk i)
    (testProjection B hZ hX hT p hk i A a ha)
    (specialArrow B hZ p hk i iΛ A a ha)
    (specialArrow_projection B hZ hX hT p hk i iΛ A a ha)
  exact h

end M9Native.CurveClassifierPullback

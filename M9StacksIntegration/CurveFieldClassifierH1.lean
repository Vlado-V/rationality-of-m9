module

public import M9StacksIntegration.CurveFieldClassifierClass
public import M9StacksIntegration.CurveFieldProjectionCoordinates
public import M9StacksIntegration.CurveFieldTargetTangent

/-!
# Actual field classifier values in the original scheme tangent model

The literal field-to-small projection of the pulled field object has the
same original family and special arrow as the native 0DZU image of the
actual pulled scheme deformation. This proves the native tangent-class
comparison; it is not an input to the H1 coordinates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin
open Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

universe u
namespace M9Native.CurveFieldClassifierH1

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K))

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p

variable {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  (i : Spec (.of k) ⟶ T)
  [IsCurve k (ParameterFamilyDeformation.fibre p i).hom]

local instance fibreProper : IsProper (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (IsProper (pullback.snd p i))
local instance fibreSmooth : Smooth (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (Smooth (pullback.snd p i))

open CurveFieldClassifierPullback CurveFieldClassifierDeformation

variable (A : ArtinianLocalAlgCat.{u,u,u} k k) (a : baseSpec A ⟶ T)
  (ha : residueSpecMap A ≫ a = i)

/-- The projected pulled field object is the ORIGINAL 0DZU/small object,
with the same original Artinian algebra and marking. -/
theorem projected_fieldObject_eq :
    letI := (targetDeformations B hZ hK hAlg p s hk i).category
    letI := (CurveFormalSmall.predeformation B hZ hk
      (ParameterFamilyDeformation.fibre p i).hom).category
    (CurveFieldTargetTangent.fieldToSmall B hZ hK hAlg hk (i ≫ s)
        (ParameterFamilyDeformation.fibre p i).hom).toFunctor.obj
      (fieldObject B hZ hK hAlg p s hk i A a ha) =
    (CurveFieldTargetTangent.schemeToSmall B hZ hk
        (ParameterFamilyDeformation.fibre p i).hom).toFunctor.obj
      (ParameterFamilyDeformation.deformation p i A a ha) := by
  let := (targetDeformations B hZ hK hAlg p s hk i).category
  let := (CurveFormalSmall.predeformation B hZ hk
    (ParameterFamilyDeformation.fibre p i).hom).category
  let d := (CurveFieldTargetTangent.fieldToSmall B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom).toFunctor.obj
    (fieldObject B hZ hK hAlg p s hk i A a ha)
  let e := (CurveFieldTargetTangent.schemeToSmall B hZ hk
      (ParameterFamilyDeformation.fibre p i).hom).toFunctor.obj
    (ParameterFamilyDeformation.deformation p i A a ha)
  have hp : d.point = e.point :=
    CurveFieldProjectionCoordinates.object_point B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom
      (fieldObject B hZ hK hAlg p s hk i A a ha)
  have hmark := CurveFieldProjectionCoordinates.object_arrow B hZ hK hAlg hk (i ≫ s)
    (ParameterFamilyDeformation.fibre p i).hom
    (fieldObject B hZ hK hAlg p s hk i A a ha)
  have he : e.arrow = (curvesSmallEquivalenceOver B hZ).hom.functor.map
      (CurveClassifierPullback.specialArrow B hZ p hk i
        (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) A a ha) := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  have hproj : (CurveFieldProjectionCoordinates.smallProjection B hZ hK hAlg).map
      (specialArrow B hZ hK hAlg p s hk i A a ha) =
      (curvesSmallEquivalenceOver B hZ).hom.functor.map
        (CurveClassifierPullback.specialArrow B hZ p hk i
          (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) A a ha) :=
    CurveFieldFamilyArrow.arrow_smallProjection B hZ hK hAlg
      (Q := CurveClassifierPullback.pointFamily B hZ p hk i)
      (R := CurveClassifierPullback.testFamily B hZ p hk i A a ha)
      (pointStructure s i) (testStructure s i A)
      (CurveClassifierPullback.specialArrow B hZ p hk i
        (B.inclusion.map (CurveFormalToCurves.integerBaseArrow B hZ hk)) A a ha)
      (special_ground B hZ p s hk i A a ha)
  have hdA : d.algebra = A :=
    BasedFunctor.w_obj (CurveFieldTargetTangent.fieldToSmall B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom)
      (fieldObject B hZ hK hAlg p s hk i A a ha)
  have heA : e.algebra = A :=
    BasedFunctor.w_obj (CurveFieldTargetTangent.schemeToSmall B hZ hk
      (ParameterFamilyDeformation.fibre p i).hom)
      (ParameterFamilyDeformation.deformation p i A a ha)
  apply deformationObject_ext_of_arrow (a := d) (b := e) (hdA.trans heA.symm) hp
  rw [he]
  exact hmark.trans (congrArg (· ≫ eqToHom hp.symm) hproj)

/-- This is an isomorphism in the SAME native Artinian fibre. -/
def projectedFieldIso :
    letI := (targetDeformations B hZ hK hAlg p s hk i).category
    letI := (CurveFormalSmall.predeformation B hZ hk
      (ParameterFamilyDeformation.fibre p i).hom).category
    (fiberFunctor (CurveFieldTargetTangent.fieldToSmall B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom) A).obj
        (fieldFiber B hZ hK hAlg p s hk i A a ha) ≅
    (fiberFunctor (CurveFieldTargetTangent.schemeToSmall B hZ hk
      (ParameterFamilyDeformation.fibre p i).hom) A).obj
        (ParameterFamilyDeformation.fibreObject p i A a ha) := by
  letI := (targetDeformations B hZ hK hAlg p s hk i).category
  letI := (CurveFormalSmall.predeformation B hZ hk
    (ParameterFamilyDeformation.fibre p i).hom).category
  exact eqToIso (Subtype.ext (projected_fieldObject_eq B hZ hK hAlg p s hk i A a ha))

variable (hfinite : LocallyOfFiniteType (i ≫ s)) (hqc : QuasiCompact (i ≫ s))
  (W : FGModuleCat.{u} k)

/-- The original pulled field family has the native class of the genuine
three-stage comparison applied to the ORIGINAL pulled scheme family. -/
theorem fieldFiber_tangent_class
    (a : baseSpec (coordBase (Λ := k) W) ⟶ T)
    (ha : residueSpecMap (coordBase (Λ := k) W) ≫ a = i) :
    letI := (targetDeformations B hZ hK hAlg p s hk i).category
    tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (targetDeformations B hZ hK hAlg p s hk i).projection)
        (CurveFieldTargetTangent.deformationStructure B hZ hK hAlg hk (i ≫ s)
          (ParameterFamilyDeformation.fibre p i).hom hfinite hqc) W
        (fieldFiber B hZ hK hAlg p s hk i (coordBase (Λ := k) W) a ha) =
      CurveFieldTargetTangent.tangentEquivalence B hZ hK hAlg hk (i ≫ s)
        (ParameterFamilyDeformation.fibre p i).hom hfinite hqc W
        (tangentClassAt.{u,u,u}
          (schemeDeformationBased (Λ := k) (ParameterFamilyDeformation.fibre p i))
          (isDeformationCategory_schemeDeformationCategoryProjection
            (ParameterFamilyDeformation.fibre p i)) W
          (ParameterFamilyDeformation.fibreObject p i (coordBase (Λ := k) W) a ha)) := by
  let := (targetDeformations B hZ hK hAlg p s hk i).category
  let := (CurveFormalSmall.predeformation B hZ hk
    (ParameterFamilyDeformation.fibre p i).hom).category
  have hE := CurveFieldTargetTangent.tangentEquivalence_tangentClassAt
    B hZ hK hAlg hk (i ≫ s) (ParameterFamilyDeformation.fibre p i).hom hfinite hqc W
    (ParameterFamilyDeformation.fibreObject p i (coordBase (Λ := k) W) a ha)
  have hclass := (CurveFieldTargetTangent.fieldClass_eq_iff_projection_isomorphic
    B hZ hK hAlg hk (i ≫ s) (ParameterFamilyDeformation.fibre p i).hom hfinite hqc W
    (fieldFiber B hZ hK hAlg p s hk i (coordBase (Λ := k) W) a ha)
    ((fiberFunctor (CurveFieldTargetComparison.basedComparison B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom) (coordBase (Λ := k) W)).obj
      (ParameterFamilyDeformation.fibreObject p i (coordBase (Λ := k) W) a ha))).mpr
    ⟨projectedFieldIso B hZ hK hAlg p s hk i (coordBase (Λ := k) W) a ha ≪≫
      (CurveFieldTargetTangent.projectedImageIso B hZ hK hAlg hk (i ≫ s)
        (ParameterFamilyDeformation.fibre p i).hom (coordBase (Λ := k) W)
        (ParameterFamilyDeformation.fibreObject p i (coordBase (Λ := k) W) a ha)).symm⟩
  exact hclass.trans hE.symm

variable (hX : B.Contains X) (hT : B.Contains T)

/-- The actual field classifier differential on a genuine test is the
original native scheme-deformation class, with the exact coefficients. -/
theorem classified_tangent_class
    (a : baseSpec (coordBase (Λ := k) W) ⟶ T)
    (ha : residueSpecMap (coordBase (Λ := k) W) ≫ a = i)
    (haS : a ≫ s = Spec.map (CommRingCat.ofHom
      (algebraMap k (coordBase (Λ := k) W))) ≫ (i ≫ s)) :
    letI := (targetDeformations B hZ hK hAlg p s hk i).category
    tangentClassAt.{u,u,u}
        (BasedCategory.ofFunctor (targetDeformations B hZ hK hAlg p s hk i).projection)
        (CurveFieldTargetTangent.deformationStructure B hZ hK hAlg hk (i ≫ s)
          (ParameterFamilyDeformation.fibre p i).hom hfinite hqc) W
        (CurveFieldClassifierClass.classifiedFiber B hZ hK hAlg hX hT p s hk i
          (coordBase (Λ := k) W) a ha haS) =
      CurveFieldTargetTangent.tangentEquivalence B hZ hK hAlg hk (i ≫ s)
        (ParameterFamilyDeformation.fibre p i).hom hfinite hqc W
        (tangentClassAt.{u,u,u}
          (schemeDeformationBased (Λ := k) (ParameterFamilyDeformation.fibre p i))
          (isDeformationCategory_schemeDeformationCategoryProjection
            (ParameterFamilyDeformation.fibre p i)) W
          (ParameterFamilyDeformation.fibreObject p i (coordBase (Λ := k) W) a ha)) := by
  let := (targetDeformations B hZ hK hAlg p s hk i).category
  have h := (tangentClassAt_eq_iff.{u,u,u}
    (BasedCategory.ofFunctor (targetDeformations B hZ hK hAlg p s hk i).projection)
    (CurveFieldTargetTangent.deformationStructure B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom hfinite hqc) W _ _).mpr
    ⟨CurveFieldClassifierClass.comparisonIso B hZ hK hAlg hX hT p s hk i
      (coordBase (Λ := k) W) a ha haS⟩
  exact h.trans (fieldFiber_tangent_class B hZ hK hAlg p s hk i hfinite hqc W a ha)

end M9Native.CurveFieldClassifierH1

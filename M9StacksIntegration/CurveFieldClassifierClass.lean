module

public import M9StacksIntegration.CurveFieldClassifierDeformation

/-!
# The genuine marked Artinian-fibre class of the field classifier

The canonical cartesian comparison is an isomorphism in the SAME native
Artinian fibre. It uses the original pulled field family and original
special arrow, rather than a stipulated deformation-class formula.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin
open Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

universe u
namespace M9Native.CurveFieldClassifierClass

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K))

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p

local instance fieldFibered :
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsFibered :=
  (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.property.isFibered


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
  (haS : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ (i ≫ s))

/-- The actual native field-classifier value in its original Artinian fibre. -/
def classifiedFiber : (targetDeformations B hZ hK hAlg p s hk i).projection.Fiber A :=
  (fiberFunctor (classifyingBased B hZ hK hAlg hX hT p s hk i) A).obj
    ⟨parameterTest B hZ hK hX hT p s hk i A a ha haS, rfl⟩

/-- The canonical test inverse is vertical over the original test base. -/
theorem testValueIso_inv_isHomLift :
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsHomLift
      (𝟙 (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)).left)
      (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS).inv := by
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)).hom
      (testProjection B hZ hK hAlg hX hT p s hk i A a ha haS) := by
    change (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (testBase B hZ hK hX hT p s hk i A a ha haS) _
    exact testProjection_cartesian B hZ hK hAlg hX hT p s hk i A a ha haS
  have h := FiberedClassifierCartesianValue.valueIso_hom_lift
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (base B hZ hK hX hT p s)
    (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK hAlg
      (originalFamily B hZ hX hT p) s)
    (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS))
    (testProjection B hZ hK hAlg hX hT p s hk i A a ha haS)
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsHomLift
      (𝟙 (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)).left)
      (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS).hom := h
  exact IsHomLift.lift_id_inv
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)).left
    (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS)

/-- A genuine native deformation morphism fixing the original coefficient algebra. -/
def comparisonMorphism :
    (classifiedFiber B hZ hK hAlg hX hT p s hk i A a ha haS).val ⟶
      (fieldFiber B hZ hK hAlg p s hk i A a ha).val where
  ringHom := 𝟙 A
  arrow := (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS).inv
  triangle := by
    change specialArrow B hZ hK hAlg p s hk i A a ha ≫
        (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS).inv =
      (pointValueIso B hZ hK hAlg hX hT p s hk i).inv ≫
        (classifier B hZ hK hAlg hX hT p s).toFunctor.map
          (specialBaseArrow B hZ hK hX hT p s hk i A a ha haS)
    rw [← testValueIso_marked B hZ hK hAlg hX hT p s hk i A a ha haS]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  arrow_base := by
    have := testValueIso_inv_isHomLift B hZ hK hAlg hX hT p s hk i A a ha haS
    let D := targetDeformations B hZ hK hAlg p s hk i
    let d := D.objects (classifiedFiber B hZ hK hAlg hX hT p s hk i A a ha haS).val
    let e := D.objects (fieldFiber B hZ hK hAlg p s hk i A a ha).val
    have hmap := CurveClassifierDeformation.post_map_eqToHom_of_vertical
      (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p (Over.post B.inclusion)
      (Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)).left
      (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS).inv e.base d.base
    change eqToHom (congrArg Over.left e.base).symm ≫
      (((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p ⋙
        Over.post B.inclusion).map
        (testValueIso B hZ hK hAlg hX hT p s hk i A a ha haS).inv).left ≫
      eqToHom (congrArg Over.left d.base) = _
    rw [hmap, Over.eqToHom_left]
    change _ = Spec.map (CommRingCat.ofHom (RingHom.id A))
    rw [CommRingCat.ofHom_id, Spec.map_id]
    simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl

omit [SmoothOfRelativeDimension 1 p] in
/-- The true field target is cofibered, without any finite-type-to-integers hypothesis. -/
theorem projection_cofibered :
    IsCofiberedInGroupoids (targetDeformations B hZ hK hAlg p s hk i).projection :=
  (CurveFieldTargetComparison.predeformationStructure B hZ hK hAlg hk (i ≫ s)
    (ParameterFamilyDeformation.fibre p i).hom).cofibered

/-- The comparison fixes the same original Artinian algebra. -/
theorem comparisonMorphism_isHomLift :
    (targetDeformations B hZ hK hAlg p s hk i).projection.IsHomLift (𝟙 A)
      (comparisonMorphism B hZ hK hAlg hX hT p s hk i A a ha haS) :=
  Functor.IsHomLift.map
    (p := (targetDeformations B hZ hK hAlg p s hk i).projection)
    (comparisonMorphism B hZ hK hAlg hX hT p s hk i A a ha haS)

/-- Hence it is an isomorphism in the SAME original native Artinian fibre. -/
def comparisonIso : classifiedFiber B hZ hK hAlg hX hT p s hk i A a ha haS ≅
    fieldFiber B hZ hK hAlg p s hk i A a ha := by
  let m := comparisonMorphism B hZ hK hAlg hX hT p s hk i A a ha haS
  have hm := comparisonMorphism_isHomLift B hZ hK hAlg hX hT p s hk i A a ha haS
  have : IsIso ((targetDeformations B hZ hK hAlg p s hk i).projection.map m) := by
    change IsIso (𝟙 A)
    infer_instance
  have : IsIso m := isIso_of_isCofiberedInGroupoids_of_map_isIso
    (projection_cofibered B hZ hK hAlg p s hk i) m
  have hi : (targetDeformations B hZ hK hAlg p s hk i).projection.IsHomLift (𝟙 A) (inv m) :=
    IsHomLift.lift_id_inv_isIso (targetDeformations B hZ hK hAlg p s hk i).projection A m
  exact
    { hom := ⟨m, hm⟩
      inv := ⟨inv m, hi⟩
      hom_inv_id := Functor.Fiber.hom_ext (IsIso.hom_inv_id m)
      inv_hom_id := Functor.Fiber.hom_ext (IsIso.inv_hom_id m) }

end M9Native.CurveFieldClassifierClass

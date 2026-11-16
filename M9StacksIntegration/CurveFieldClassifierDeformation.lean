module

public import M9StacksIntegration.CurveFieldClassifierPullback
public import M9StacksIntegration.CurveClassifierDeformation

/-!
# The actual field-family classifying functor on pointed deformations

The original field classifier is transported by the canonical cartesian
point-value isomorphism. The test and the pulled field deformation use the
same original Artinian algebra and the same original marked special arrow.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin
open Deformation.Examples
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

universe u
namespace M9Native.CurveFieldClassifierDeformation

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

open CurveFieldClassifierPullback

/-- The actual represented parameter point has its original coefficient/ground base. -/
theorem parameterPoint_base :
    (Over.forget (base B hZ hK hX hT p s) ⋙ Over.post B.inclusion).obj
        (parameterPoint B hZ hK hX hT p s hk i) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ (i ≫ s)) := rfl

/-- Its native represented point map is precisely the original scheme point. -/
theorem parameterPoint_map : SliceTangent.pointMap
    (parameterPoint_base B hZ hK hX hT p s hk i) = i := by
  change 𝟙 _ ≫ i = i
  exact Category.id_comp i

abbrev parameterDeformations := predeformationCategory (i ≫ s)
  (Over.forget (base B hZ hK hX hT p s) ⋙ Over.post B.inclusion)
  (parameterPoint B hZ hK hX hT p s hk i)
  (parameterPoint_base B hZ hK hX hT p s hk i)

instance parameterCategory : Category
    (parameterDeformations B hZ hK hX hT p s hk i).carrier :=
  (parameterDeformations B hZ hK hX hT p s hk i).category

abbrev targetDeformations := CurveFieldTargetComparison.predeformation B hZ hK hAlg hk (i ≫ s)
  (ParameterFamilyDeformation.fibre p i).hom

instance targetCategory : Category (targetDeformations B hZ hK hAlg p s hk i).carrier :=
  (targetDeformations B hZ hK hAlg p s hk i).category

/-- The true point comparison is vertical over exactly the original coefficient base. -/
theorem pointValueIso_inv_isHomLift :
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsHomLift
      (𝟙 (parameterPoint B hZ hK hX hT p s hk i).left)
      (pointValueIso B hZ hK hAlg hX hT p s hk i).inv := by
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (parameterPoint B hZ hK hX hT p s hk i).hom
      (pointProjection B hZ hK hAlg hX hT p s hk i) := by
    change (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (pointBase B hZ hK hX hT p s hk i) _
    exact pointProjection_cartesian B hZ hK hAlg hX hT p s hk i
  have h := FiberedClassifierCartesianValue.valueIso_hom_lift
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (base B hZ hK hX hT p s)
    (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK hAlg
      (originalFamily B hZ hX hT p) s)
    (parameterPoint B hZ hK hX hT p s hk i)
    (pointProjection B hZ hK hAlg hX hT p s hk i)
  have : (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.IsHomLift
      (𝟙 (parameterPoint B hZ hK hX hT p s hk i).left)
      (pointValueIso B hZ hK hAlg hX hT p s hk i).hom := h
  exact IsHomLift.lift_id_inv
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (parameterPoint B hZ hK hX hT p s hk i).left
    (pointValueIso B hZ hK hAlg hX hT p s hk i)

/-- The actual point inverse has exactly the native transport base map. -/
theorem pointValueIso_inv_base :
    ((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p ⋙
        Over.post B.inclusion).map (pointValueIso B hZ hK hAlg hX hT p s hk i).inv =
      eqToHom
        ((CurveFieldTargetComparison.fieldPoint_lies_over B hZ hK hAlg hk (i ≫ s)
            (ParameterFamilyDeformation.fibre p i).hom).trans
          ((transport_obj_eq B hK (Over.forget (base B hZ hK hX hT p s))
            (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
            (classifier B hZ hK hAlg hX hT p s).toFunctor
            (classifier B hZ hK hAlg hX hT p s).w
            (parameterPoint B hZ hK hX hT p s hk i)).trans
              (parameterPoint_base B hZ hK hX hT p s hk i)).symm) := by
  have := pointValueIso_inv_isHomLift B hZ hK hAlg hX hT p s hk i
  exact CurveClassifierDeformation.post_map_eqToHom_of_vertical
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p (Over.post B.inclusion)
    (parameterPoint B hZ hK hX hT p s hk i).left
    (pointValueIso B hZ hK hAlg hX hT p s hk i).inv
    (CurveFieldTargetComparison.fieldPoint_lies_over B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom)
    ((transport_obj_eq B hK (Over.forget (base B hZ hK hX hT p s))
      (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
      (classifier B hZ hK hAlg hX hT p s).toFunctor
      (classifier B hZ hK hAlg hX hT p s).w
      (parameterPoint B hZ hK hX hT p s hk i)).trans
        (parameterPoint_base B hZ hK hX hT p s hk i))

/-- The actual field classifying functor on original pointed deformations. -/
def classifyingFunctor : (parameterDeformations B hZ hK hX hT p s hk i).carrier ⥤
    (targetDeformations B hZ hK hAlg p s hk i).carrier :=
  transportPredeformationFunctor B hK (i ≫ s)
    (Over.forget (base B hZ hK hX hT p s))
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (classifier B hZ hK hAlg hX hT p s).toFunctor
    (classifier B hZ hK hAlg hX hT p s).w
    (parameterPoint B hZ hK hX hT p s hk i)
    (parameterPoint_base B hZ hK hX hT p s hk i)
    (CurveFieldTargetComparison.fieldPoint B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom)
    (CurveFieldTargetComparison.fieldPoint_lies_over B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom)
    (pointValueIso B hZ hK hAlg hX hT p s hk i).inv
    (pointValueIso_inv_base B hZ hK hAlg hX hT p s hk i)

/-- The original Artinian projection is unchanged. -/
def classifyingBased :
    BasedCategory.ofFunctor (parameterDeformations B hZ hK hX hT p s hk i).projection ⥤ᵇ
      BasedCategory.ofFunctor (targetDeformations B hZ hK hAlg p s hk i).projection where
  toFunctor := classifyingFunctor B hZ hK hAlg hX hT p s hk i
  w := transportPredeformationFunctor_comp_projection B hK (i ≫ s)
    (Over.forget (base B hZ hK hX hT p s))
    (CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p
    (classifier B hZ hK hAlg hX hT p s).toFunctor
    (classifier B hZ hK hAlg hX hT p s).w
    (parameterPoint B hZ hK hX hT p s hk i)
    (parameterPoint_base B hZ hK hX hT p s hk i)
    (CurveFieldTargetComparison.fieldPoint B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom)
    (CurveFieldTargetComparison.fieldPoint_lies_over B hZ hK hAlg hk (i ≫ s)
      (ParameterFamilyDeformation.fibre p i).hom)
    (pointValueIso B hZ hK hAlg hX hT p s hk i).inv
    (pointValueIso_inv_base B hZ hK hAlg hX hT p s hk i)

variable (A : ArtinianLocalAlgCat.{u,u,u} k k) (a : baseSpec A ⟶ T)
  (ha : residueSpecMap A ≫ a = i)
  (haS : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫ (i ≫ s))

/-- The literal original represented test over the actual field base. -/
def parameterTest : (parameterDeformations B hZ hK hX hT p s hk i).carrier where
  algebra := A
  point := Over.mk (testBase B hZ hK hX hT p s hk i A a ha haS)
  arrow := specialBaseArrow B hZ hK hX hT p s hk i A a ha haS
  base := rfl
  arrow_base := by
    change 𝟙 _ ≫ residueSpecMap A ≫ 𝟙 _ = _
    simp

/-- The native represented test map is precisely the given original test arrow. -/
theorem parameterTest_map : SliceTangent.deformationMap
    (parameterTest B hZ hK hX hT p s hk i A a ha haS) = a := by
  change 𝟙 _ ≫ a = a
  exact Category.id_comp a

/-- The actual pulled field deformation, carrying the ORIGINAL special arrow. -/
def fieldObject : (targetDeformations B hZ hK hAlg p s hk i).carrier where
  algebra := A
  point := testFamily B hZ hK hAlg p s hk i A a ha
  arrow := specialArrow B hZ hK hAlg p s hk i A a ha
  base := CurveFieldClassifyingFamily.fieldFamily_post B hZ hK hAlg
    (CurveClassifierPullback.testFamily B hZ p hk i A a ha) (testStructure s i A)
  arrow_base := by
    change 𝟙 _ ≫ B.inclusion.map
      (((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.map
        (specialArrow B hZ hK hAlg p s hk i A a ha)).left) ≫ 𝟙 _ = _
    change 𝟙 _ ≫ B.inclusion.map
      (((CurveFieldClassifyingFamily.fieldStack B hZ hK hAlg).val.val.p.map
        (CurveFieldFamilyArrow.arrow _ _ _ _ _ _ _ _)).left) ≫ 𝟙 _ = _
    rw [CurveFieldFamilyArrow.arrow_base]
    simp only [CurveFieldFamilyArrow.projectedBaseArrow, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- The corresponding object of the SAME original Artinian fibre. -/
def fieldFiber : (targetDeformations B hZ hK hAlg p s hk i).projection.Fiber A :=
  ⟨fieldObject B hZ hK hAlg p s hk i A a ha, rfl⟩

end M9Native.CurveFieldClassifierDeformation

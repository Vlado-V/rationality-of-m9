module

public import M9StacksIntegration.CurveClassifierPullback
public import StacksFrontier.Deformation.Artin.Predeformation.Transport
public import StacksFrontier.Deformation.Artin.SliceTangentSpace

/-!
# Original pointed deformation classes of the actual Curves classifier

The actual classifier is transported by the canonical fibre isomorphism
proved from the original pullback. The comparison in the Artinian fibre
retains both the original algebra and the actual marked special-fibre map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Artin Deformation.Examples

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

universe u uC vC uF vF uD vD

namespace M9Native.CurveClassifierDeformation

/-- Forgetting part of the base preserves a genuine vertical arrow, with
the exact original endpoint identifications. -/
theorem post_map_eqToHom_of_vertical
    {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
    {D : Type uD} [Category.{vD} D] (p : F ⥤ C) (R : C ⥤ D)
    (A : C) {a b : F} (β : a ⟶ b) [p.IsHomLift (𝟙 A) β]
    {Z : D} (ha : (p ⋙ R).obj a = Z) (hb : (p ⋙ R).obj b = Z) :
    (p ⋙ R).map β = eqToHom (ha.trans hb.symm) := by
  change R.map (p.map β) = _
  rw [IsHomLift.fac' p (𝟙 A) β]
  simp only [eqToHom_map, Category.id_comp, eqToHom_trans]

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p
local instance curvesFibered : (curvesProjectionOver B hZ).IsFibered :=
  (curvesFiberedCategory B hZ).property.isFibered

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (hk : B.Contains (Spec (.of k))) (i : Spec (.of k) ⟶ T)
  [IsCurve k (ParameterFamilyDeformation.fibre p i).hom]
  (iΛ : Spec (.of Λ) ⟶ integerBase)

local instance fibreProper : IsProper (ParameterFamilyDeformation.fibre p i).hom :=
  inferInstanceAs (IsProper (pullback.snd p i))

/-- The original represented base of the actual scheme family. -/
abbrev parameter := integerSiteObject B hZ hT

/-- The represented point given by the actual original special fibre. -/
abbrev parameterPoint : Over (parameter B hZ hT) :=
  Over.mk (CurveClassifierPullback.pointProjection B hZ hX hT p hk i).baseMap

/-- Its base is the original residue spectrum and original integer structure map. -/
theorem parameterPoint_base :
    (Over.forget (parameter B hZ hT) ⋙ Over.post B.inclusion).obj
        (parameterPoint B hZ hX hT p hk i) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
  post_integerSiteObject hk _

/-- The original represented-point predeformation category. -/
abbrev parameterDeformations :=
  predeformationCategory iΛ
    (Over.forget (parameter B hZ hT) ⋙ Over.post B.inclusion)
    (parameterPoint B hZ hX hT p hk i)
    (parameterPoint_base B hZ hX hT p hk i iΛ)

instance parameterCategory : Category (parameterDeformations B hZ hX hT p hk i iΛ).carrier :=
  (parameterDeformations B hZ hX hT p hk i iΛ).category

/-- The original native point of Curves is exactly the actual scheme fibre. -/
abbrev curvePoint := CurveClassifierPullback.pointFamily B hZ p hk i

/-- The exact original Curves deformation category of that fibre. -/
abbrev curveDeformations :=
  curvesPredeformation B hZ (ParameterFamilyDeformation.fibre p i) hk
    (CurveClassifierPullback.fibre_dimension p i) iΛ

/-- The canonical marked-fibre identification is vertical over the original field base. -/
theorem pointValueIso_inv_isHomLift :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 (parameterPoint B hZ hX hT p hk i).left)
      (CurveClassifierPullback.pointValueIso B hZ hX hT p hk i).inv := by
  have : (curvesProjectionOver B hZ).IsStronglyCartesian
      (parameterPoint B hZ hX hT p hk i).hom
      (CurveClassifierPullback.pointProjection B hZ hX hT p hk i) := by
    change (curvesProjectionOver B hZ).IsStronglyCartesian
      (CurveClassifierPullback.pointProjection B hZ hX hT p hk i).baseMap _
    exact CurveClassifierPullback.originalCurveCartesian B hZ _
  have h := FiberedClassifierCartesianValue.valueIso_hom_lift
    (curvesProjectionOver B hZ) (parameter B hZ hT) rfl
    (parameterPoint B hZ hX hT p hk i)
    (CurveClassifierPullback.pointProjection B hZ hX hT p hk i)
  have : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 (parameterPoint B hZ hX hT p hk i).left)
      (CurveClassifierPullback.pointValueIso B hZ hX hT p hk i).hom := h
  exact IsHomLift.lift_id_inv (curvesProjectionOver B hZ)
    (parameterPoint B hZ hX hT p hk i).left
    (CurveClassifierPullback.pointValueIso B hZ hX hT p hk i)

/-- The actual point isomorphism has exactly the projection used by native
base-point transport, derived from its genuine verticality. -/
theorem pointValueIso_inv_base :
    (curvesToSchemesOver B hZ).map
        (CurveClassifierPullback.pointValueIso B hZ hX hT p hk i).inv =
      eqToHom
        ((curvesToSchemesOver_obj_curveFamilyOfScheme
            (ParameterFamilyDeformation.fibre p i) B hZ hk
            (CurveClassifierPullback.fibre_dimension p i) iΛ).trans
          ((transport_obj_eq B hZ (Over.forget (parameter B hZ hT))
            (curvesProjectionOver B hZ)
            (CurveClassifierPullback.classifier B hZ hX hT p).toFunctor
            (CurveClassifierPullback.classifier B hZ hX hT p).w
            (parameterPoint B hZ hX hT p hk i)).trans
              (parameterPoint_base B hZ hX hT p hk i iΛ)).symm) := by
  have := pointValueIso_inv_isHomLift B hZ hX hT p hk i
  exact post_map_eqToHom_of_vertical (curvesProjectionOver B hZ)
    (Over.post B.inclusion) (parameterPoint B hZ hX hT p hk i).left
    (CurveClassifierPullback.pointValueIso B hZ hX hT p hk i).inv
    (curvesToSchemesOver_obj_curveFamilyOfScheme (ParameterFamilyDeformation.fibre p i)
      B hZ hk (CurveClassifierPullback.fibre_dimension p i) iΛ)
    ((transport_obj_eq B hZ (Over.forget (parameter B hZ hT))
      (curvesProjectionOver B hZ)
      (CurveClassifierPullback.classifier B hZ hX hT p).toFunctor
      (CurveClassifierPullback.classifier B hZ hX hT p).w
      (parameterPoint B hZ hX hT p hk i)).trans
        (parameterPoint_base B hZ hX hT p hk i iΛ))

/-- The native classifying functor on pointed deformations, transported by
the proved canonical fibre isomorphism. -/
def classifyingFunctor :
    (parameterDeformations B hZ hX hT p hk i iΛ).carrier ⥤
      (curveDeformations B hZ p hk i iΛ).carrier :=
  transportPredeformationFunctor B hZ iΛ
    (Over.forget (parameter B hZ hT)) (curvesProjectionOver B hZ)
    (CurveClassifierPullback.classifier B hZ hX hT p).toFunctor
    (CurveClassifierPullback.classifier B hZ hX hT p).w
    (parameterPoint B hZ hX hT p hk i)
    (parameterPoint_base B hZ hX hT p hk i iΛ)
    (curvePoint B hZ p hk i)
    (curvesToSchemesOver_obj_curveFamilyOfScheme (ParameterFamilyDeformation.fibre p i)
      B hZ hk (CurveClassifierPullback.fibre_dimension p i) iΛ)
    (CurveClassifierPullback.pointValueIso B hZ hX hT p hk i).inv
    (pointValueIso_inv_base B hZ hX hT p hk i iΛ)

/-- This is an actual functor over the unchanged Artinian category. -/
def classifyingBased :
    BasedCategory.ofFunctor (parameterDeformations B hZ hX hT p hk i iΛ).projection ⥤ᵇ
      BasedCategory.ofFunctor (curveDeformations B hZ p hk i iΛ).projection where
  toFunctor := classifyingFunctor B hZ hX hT p hk i iΛ
  w := transportPredeformationFunctor_comp_projection B hZ iΛ
    (Over.forget (parameter B hZ hT)) (curvesProjectionOver B hZ)
    (CurveClassifierPullback.classifier B hZ hX hT p).toFunctor
    (CurveClassifierPullback.classifier B hZ hX hT p).w
    (parameterPoint B hZ hX hT p hk i)
    (parameterPoint_base B hZ hX hT p hk i iΛ)
    (curvePoint B hZ p hk i)
    (curvesToSchemesOver_obj_curveFamilyOfScheme (ParameterFamilyDeformation.fibre p i)
      B hZ hk (CurveClassifierPullback.fibre_dimension p i) iΛ)
    (CurveClassifierPullback.pointValueIso B hZ hX hT p hk i).inv
    (pointValueIso_inv_base B hZ hX hT p hk i iΛ)

/-- The literal parameter test in the original represented source, using
the actual marked base arrow already constructed from the pullback. -/
def parameterTest (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (parameterDeformations B hZ hX hT p hk i iΛ).carrier where
  algebra := A
  point := Over.mk (CurveClassifierPullback.testProjection B hZ hX hT p hk i A a ha).baseMap
  arrow := CurveClassifierPullback.specialBaseArrow B hZ hX hT p hk i iΛ A a ha
  base := post_integerSiteObject (contains_baseSpec B hk A) _
  arrow_base := by
    change 𝟙 _ ≫ residueSpecMap A ≫ 𝟙 _ = _
    simp

/-- Reading the native represented test returns exactly the original arrow. -/
theorem parameterTest_map (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    SliceTangent.deformationMap (parameterTest B hZ hX hT p hk i iΛ A a ha) = a := by
  change 𝟙 _ ≫ a = a
  exact Category.id_comp a

end M9Native.CurveClassifierDeformation

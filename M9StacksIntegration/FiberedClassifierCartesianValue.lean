module

public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered

/-!
# Actual cartesian values of the native two-Yoneda classifier

The classifier is the original `OfFiberObj.fiberedMor`. A specified
cartesian arrow to its original family determines its value by the real
universal property. The comparison also preserves the arrows of pointed
deformation diagrams.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe uC vC uF vF

namespace M9Native.FiberedClassifierCartesianValue

variable {C : Type uC} [Category.{vC} C]
  {F : Type uF} [Category.{vF} F]
  (p : F ⥤ C) [p.IsFibered] (U : C) {y : F} (hy : p.obj y = U)

/-- The literal native two-Yoneda classifying morphism of the original object. -/
abbrev classifier := FiberedMor.OfFiberObj.fiberedMor p U hy

/-- Its actual projection to the original family. -/
abbrev projection (x : Over U) : (classifier p U hy).toFunctor.obj x ⟶ y :=
  IsPreFibered.pullbackMap hy x.hom

/-- The classifier value is canonically vertically isomorphic to any
actual cartesian lift of the same original family. -/
def valueIso (x : Over U) {z : F} (ρ : z ⟶ y)
    [p.IsStronglyCartesian x.hom ρ] : (classifier p U hy).toFunctor.obj x ≅ z :=
  IsStronglyCartesian.domainIsoOfBaseIso p
    (show x.hom = (Iso.refl x.left).hom ≫ x.hom by simp)
    ρ (projection p U hy x)

/-- The comparison lies over the identity of the original test object. -/
theorem valueIso_hom_lift (x : Over U) {z : F} (ρ : z ⟶ y)
    [p.IsStronglyCartesian x.hom ρ] :
    p.IsHomLift (𝟙 x.left) (valueIso p U hy x ρ).hom := by
  exact inferInstanceAs (p.IsHomLift (Iso.refl x.left).hom
    (IsStronglyCartesian.domainIsoOfBaseIso p
      (show x.hom = (Iso.refl x.left).hom ≫ x.hom by simp)
      ρ (projection p U hy x)).hom)

/-- It preserves the actual projection to the original family. -/
theorem valueIso_fac (x : Over U) {z : F} (ρ : z ⟶ y)
    [p.IsStronglyCartesian x.hom ρ] :
    (valueIso p U hy x ρ).hom ≫ ρ = projection p U hy x :=
  IsStronglyCartesian.fac p x.hom ρ
    (show x.hom = (Iso.refl x.left).hom ≫ x.hom by simp)
    (projection p U hy x)

/-- Every actual compatible arrow of cartesian lifts is the arrow induced
by the native classifier, under these canonical vertical isomorphisms. -/
theorem valueIso_naturality {x₀ x₁ : Over U} (α : x₀ ⟶ x₁)
    {z₀ z₁ : F} (ρ₀ : z₀ ⟶ y) (ρ₁ : z₁ ⟶ y)
    [p.IsStronglyCartesian x₀.hom ρ₀] [p.IsStronglyCartesian x₁.hom ρ₁]
    (δ : z₀ ⟶ z₁) [p.IsHomLift α.left δ] (hδ : δ ≫ ρ₁ = ρ₀) :
    (classifier p U hy).toFunctor.map α ≫ (valueIso p U hy x₁ ρ₁).hom =
      (valueIso p U hy x₀ ρ₀).hom ≫ δ := by
  have hα := (classifier p U hy).isHomLift_map α
  have h₀ := valueIso_hom_lift p U hy x₀ ρ₀
  have h₁ := valueIso_hom_lift p U hy x₁ ρ₁
  have hL : p.IsHomLift α.left
      ((classifier p U hy).toFunctor.map α ≫ (valueIso p U hy x₁ ρ₁).hom) :=
    IsHomLift.comp_lift_id_right p α.left _ _
  have hR : p.IsHomLift α.left ((valueIso p U hy x₀ ρ₀).hom ≫ δ) :=
    IsHomLift.comp_lift_id_left p α.left _ _
  have hfac : (classifier p U hy).toFunctor.map α ≫ projection p U hy x₁ =
      projection p U hy x₀ :=
    FiberedMor.OfFiberObj.pullbackFunctor_map_fac p U hy α
  apply IsStronglyCartesian.ext p x₁.hom ρ₁ α.left
  calc
    ((classifier p U hy).toFunctor.map α ≫ (valueIso p U hy x₁ ρ₁).hom) ≫ ρ₁ =
        (classifier p U hy).toFunctor.map α ≫ projection p U hy x₁ := by
      rw [Category.assoc, valueIso_fac]
    _ = projection p U hy x₀ := hfac
    _ = ((valueIso p U hy x₀ ρ₀).hom ≫ δ) ≫ ρ₁ := by
      rw [Category.assoc, hδ, valueIso_fac]

/-- Inverse orientation for the actual marked special-fibre arrow. -/
theorem valueIso_marked {x₀ x₁ : Over U} (α : x₀ ⟶ x₁)
    {z₀ z₁ : F} (ρ₀ : z₀ ⟶ y) (ρ₁ : z₁ ⟶ y)
    [p.IsStronglyCartesian x₀.hom ρ₀] [p.IsStronglyCartesian x₁.hom ρ₁]
    (δ : z₀ ⟶ z₁) [p.IsHomLift α.left δ] (hδ : δ ≫ ρ₁ = ρ₀) :
    (valueIso p U hy x₀ ρ₀).inv ≫ (classifier p U hy).toFunctor.map α ≫
      (valueIso p U hy x₁ ρ₁).hom = δ := by
  rw [valueIso_naturality p U hy α ρ₀ ρ₁ δ hδ]
  simp

end M9Native.FiberedClassifierCartesianValue

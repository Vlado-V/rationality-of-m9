module

public import M9StacksIntegration.FiberedClassifierCartesianValue

/-!
# Original two-Yoneda classifiers under a genuine Cartesian family arrow

A Cartesian arrow between the original families supplies the natural
isomorphism of classifiers after parameter change. Its components retain
the original family projections and lie over the identity test arrows.
No classifying-functor identity is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe uC vC uF vF

namespace M9Native.FiberedClassifierBaseChange

variable {C : Type uC} [Category.{vC} C] {E : Type uF} [Category.{vF} E]
  (p : E ⥤ C) [p.IsFibered] {U V : C} {q r : E}
  (hq : p.obj q = V) (hr : p.obj r = U) (f : V ⟶ U) (α : q ⟶ r)
  [p.IsStronglyCartesian f α]

open FiberedClassifierCartesianValue

omit [p.IsStronglyCartesian f α] in
/-- The actual projection from the changed classifier to the original
family, obtained by composing the two genuine Cartesian arrows. -/
abbrev projection (z : Over V) : (classifier p V hq).toFunctor.obj z ⟶ r :=
  FiberedClassifierCartesianValue.projection p V hq z ≫ α

instance projection_cartesian (z : Over V) :
    p.IsStronglyCartesian ((Over.map f).obj z).hom (projection p hq α z) := by
  exact inferInstanceAs (p.IsStronglyCartesian (z.hom ≫ f)
    (FiberedClassifierCartesianValue.projection p V hq z ≫ α))

/-- The original composite classifier value is determined by this actual
Cartesian lift, with no supplied identification of its value. -/
def componentIso (z : Over V) :
    (classifier p U hr).toFunctor.obj ((Over.map f).obj z) ≅
      (classifier p V hq).toFunctor.obj z :=
  valueIso p U hr ((Over.map f).obj z) (projection p hq α z)

/-- The original classifying morphism commutes with actual parameter
change up to this derived, genuine natural isomorphism. -/
def comparisonIso :
    Over.map f ⋙ (classifier p U hr).toFunctor ≅ (classifier p V hq).toFunctor :=
  NatIso.ofComponents (componentIso p hq hr f α) (by
    intro z w β
    have : p.IsHomLift ((Over.map f).map β).left
        ((classifier p V hq).toFunctor.map β) := by
      change p.IsHomLift β.left ((classifier p V hq).toFunctor.map β)
      exact (classifier p V hq).isHomLift_map β
    exact valueIso_naturality p U hr ((Over.map f).map β)
      (projection p hq α z) (projection p hq α w)
      ((classifier p V hq).toFunctor.map β) (by
        change (classifier p V hq).toFunctor.map β ≫
          (FiberedClassifierCartesianValue.projection p V hq w ≫ α) =
          FiberedClassifierCartesianValue.projection p V hq z ≫ α
        rw [← Category.assoc]
        have hfac : (classifier p V hq).toFunctor.map β ≫
            FiberedClassifierCartesianValue.projection p V hq w =
              FiberedClassifierCartesianValue.projection p V hq z :=
          FiberedMor.OfFiberObj.pullbackFunctor_map_fac p V hq β
        exact congrArg (fun a => a ≫ α) hfac))

/-- The comparison preserves the actual arrow to the original family. -/
theorem comparisonIso_fac (z : Over V) :
    (comparisonIso p hq hr f α).hom.app z ≫ projection p hq α z =
      FiberedClassifierCartesianValue.projection p U hr ((Over.map f).obj z) :=
  valueIso_fac p U hr ((Over.map f).obj z) (projection p hq α z)

/-- Its components are vertical on the same original test base. -/
theorem comparisonIso_hom_lift (z : Over V) :
    p.IsHomLift (𝟙 z.left) ((comparisonIso p hq hr f α).hom.app z) :=
  valueIso_hom_lift p U hr ((Over.map f).obj z) (projection p hq α z)

omit [p.IsFibered] [p.IsStronglyCartesian f α] in
/-- The literal parameter-change functor over the unchanged original base. -/
def parameterBased :
    BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget U) where
  toFunctor := Over.map f
  w := rfl

/-- The same derived comparison as an isomorphism of genuine based
functors. This is the actual two-isomorphism used by native stack geometry. -/
def comparisonBasedIso :
    BasedFunctor.comp (parameterBased f) (classifier p U hr).toBasedFunctor ≅
      (classifier p V hq).toBasedFunctor :=
  BasedNatIso.mkNatIso (comparisonIso p hq hr f α)
    (comparisonIso_hom_lift p hq hr f α)

end M9Native.FiberedClassifierBaseChange

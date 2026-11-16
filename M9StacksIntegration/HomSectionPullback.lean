module

public import M9StacksIntegration.CurriedHomSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal

/-!
# Actual pullback nonvanishing of the native curried Hom section

The pullback functor has its proved strong monoidal structure. The actual
unit-to-Hom morphism transported by that functor is the actual pulled-back
unit morphism of `UnitSectionPullback`; the actual associated section is
therefore `pullbackGlobalSections` of the original native Hom section.
No flatness or internal-Hom comparison isomorphism is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed

universe u

namespace M9Native.HomSectionPullback

@[instance_reducible] local instance moduleMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor X.sheaf

@[instance_reducible] local instance moduleClosed (X : Scheme.{u}) :
    MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosedSheafTensor X.sheaf

local instance moduleMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  SheafOfModules.monoidalPreadditiveSheafTensor X.sheaf

@[instance_reducible] local instance modulePullbackMonoidal {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Scheme.Modules.pullback g).Monoidal :=
  Stacks.PullbackSheafTensor.monoidal g.toLRSHom.toShHom

/-- The native monoidal unit comparison is the native structure-sheaf
pullback isomorphism, in the direction needed for transported sections. -/
theorem mappedHomSection_eq_pulledUnitMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {E F : Y.Modules} (a : E ⟶ F) :
    M9.MonoidalHomSection.mappedHomSection (Scheme.Modules.pullback g) a =
      UnitSectionPullback.pulledUnitMap g (CurriedHomSection.curriedMap a) := by
  rfl

/-- A nonzero actual pulled-back sheaf morphism has nonzero actual
pulled-back native Hom section. This is the fiberwise incidence-section
bridge, including the actual sheaf/global-section comparison. -/
theorem pullback_homSection_ne_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    {E F : Y.Modules} (a : E ⟶ F) (ha : (Scheme.Modules.pullback g).map a ≠ 0) :
    pullbackGlobalSections g (CurriedHomSection.homBundle E F)
      (CurriedHomSection.homSection a) ≠ 0 := by
  apply UnitSectionPullback.pullback_unitSection_ne_zero g (CurriedHomSection.curriedMap a)
  intro hz
  have hm := M9.MonoidalHomSection.mappedHomSection_ne_zero (Scheme.Modules.pullback g) a ha
  exact hm ((mappedHomSection_eq_pulledUnitMap g a).trans hz)

end M9Native.HomSectionPullback

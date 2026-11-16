module

public import M9.MonoidalHomSection
public import M9StacksIntegration.UnitSectionPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction

/-!
# The actual global section of the native internal Hom defined by a map

The native sheaf category carries its proved sheaf-tensor monoidal closed
structure. Currying an actual sheaf morphism gives an actual morphism
from the structure sheaf to its actual internal Hom; evaluating at the
global unit gives its actual global section. A nonzero morphism produces
a nonzero section. No section or comparison property is stored as input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed

universe u

namespace M9Native.CurriedHomSection

@[instance_reducible] local instance moduleMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor X.sheaf

@[instance_reducible] local instance moduleClosed (X : Scheme.{u}) :
    MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosedSheafTensor X.sheaf

local instance moduleMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  SheafOfModules.monoidalPreadditiveSheafTensor X.sheaf

/-- The actual internal-Hom sheaf of the native sheaf-tensor closed
category. The proved native tensor-Hom adjunction identifies this with
the sectionwise sheaf Hom. -/
def homBundle {X : Scheme.{u}} (E F : X.Modules) : X.Modules :=
  (ihom E).obj F

/-- The actual unit-to-internal-Hom morphism obtained by currying. -/
def curriedMap {X : Scheme.{u}} {E F : X.Modules} (a : E ⟶ F) :
    Stacks.Ample.unitModule X ⟶ homBundle E F :=
  curry' a

/-- The actual global Hom section defined by an actual sheaf map. -/
def homSection {X : Scheme.{u}} {E F : X.Modules} (a : E ⟶ F) :
    Γ(homBundle E F, ⊤) :=
  UnitSectionPullback.unitSection (curriedMap a)

/-- Nonzero native morphisms have nonzero actual global Hom sections. -/
theorem homSection_ne_zero {X : Scheme.{u}} {E F : X.Modules} (a : E ⟶ F)
    (ha : a ≠ 0) : homSection a ≠ 0 := by
  intro hs
  have hc : curry' a = 0 :=
    UnitSectionPullback.eq_zero_of_unitSection_eq_zero (curriedMap a) hs
  apply ha
  simpa using M9.MonoidalHomSection.map_eq_zero_of_map_curry'_eq_zero
    (𝟭 X.Modules) a (by simpa using hc)

end M9Native.CurriedHomSection

module

public import M9StacksIntegration.NativeGenericFieldPoints
public import M9StacksIntegration.PrimitiveConstantFieldAction

@[expose] public section

/-! Actual dominant morphisms act on genuine generic field points by their
actual generic-stalk pullbacks. These formulas bind the original constant
Sp6 action to its native field pullback at every extension-field embedding.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.NativeGenericPointNaturality

open NativeGenericPullbackEvaluation

/-- Genuine generic points are natural for the actual dominant pullback. -/
theorem point_comp_dominant {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (a : Y ⟶ X) [IsDominant a] {L : Type u} [Field L]
    (s : Y.functionField →+* L) :
    point s ≫ a = point (s.comp (NativeDominantFunctionField.map a)) := by
  rw [point, point, Category.assoc, ← NativeFunctionFieldFunctor.map_square a,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- This is the literal generic-point formula for the original constant
symplectic action and its actual native field pullback. -/
theorem constant_action {L : Type} [Field L]
    (s : PrimitiveGrassmannianAction.space.functionField →+* L)
    (h : PrimitiveConstantFieldAction.Sp6) :
    point s ≫ PrimitiveConstantFieldAction.schemeMap h =
      point (s.comp (PrimitiveConstantFieldAction.fieldPullback h).toRingHom) := by
  rw [PrimitiveConstantFieldAction.fieldPullback_eq_map]
  exact point_comp_dominant _ s

end M9Native.NativeGenericPointNaturality

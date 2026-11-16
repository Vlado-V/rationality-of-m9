module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The actual family fiber at an over-base point

For `X ×_S T → T` and a section `p : S → T` of `q : T → S`,
the original scheme `X` is an actual pullback along `p`. The graph
morphism and cartesian square are constructed from the genuine
pullback universal property. In the Picard application this expresses
an actual base-field point's family fiber directly on the original
curve, avoiding an unjustified extension-field nonexistence premise.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.BaseFieldGraph

variable {X S T : Scheme.{u}} (f : X ⟶ S) (q : T ⟶ S)
  (p : S ⟶ T) (hp : p ≫ q = 𝟙 S)

/-- The actual graph of the actual over-base point in the actual
base-changed family. -/
def graph : X ⟶ pullback f q :=
  pullback.lift (𝟙 X) (f ≫ p) (by simp [Category.assoc, hp])

@[simp] theorem graph_fst : graph f q p hp ≫ pullback.fst f q = 𝟙 X :=
  pullback.lift_fst _ _ _

@[simp] theorem graph_snd : graph f q p hp ≫ pullback.snd f q = f ≫ p :=
  pullback.lift_snd _ _ _

/-- The original scheme, with its actual graph, is the actual family
pullback at a point over the same base. -/
theorem isPullback_graph :
    IsPullback (graph f q p hp) f (pullback.snd f q) p := by
  have hwhole : IsPullback (graph f q p hp ≫ pullback.fst f q) f f (p ≫ q) := by
    simpa only [graph_fst, hp] using (IsPullback.of_id_fst (f := f))
  exact hwhole.of_right (graph_snd f q p hp) (IsPullback.of_hasPullback f q)

end M9Native.BaseFieldGraph

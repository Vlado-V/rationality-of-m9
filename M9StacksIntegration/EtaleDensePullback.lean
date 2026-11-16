module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Density of an actual pullback of a dense scheme map by an etale map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
namespace M9Native.EtaleDensePullback

variable {X U V P : Scheme.{u}}

/-- Etale tests preserve density of the actual represented pullback. -/
theorem denseRange_snd (j : U ⟶ X) (v : V ⟶ X) [Etale v]
    (hj : DenseRange j) : DenseRange (pullback.snd j v) := by
  change Dense (Set.range (pullback.snd j v))
  rw [Scheme.Pullback.range_snd]
  exact hj.preimage v.isOpenMap

theorem denseRange_of_isPullback (j : U ⟶ X) (v : V ⟶ X) [Etale v]
    (b : P ⟶ U) (a : P ⟶ V) (h : IsPullback b a j v)
    (hj : DenseRange j) : DenseRange a := by
  have hh := denseRange_snd j v hj
  have he : Function.Surjective h.isoPullback.hom := h.isoPullback.hom.surjective
  rw [← h.isoPullback_hom_snd]
  change Dense (Set.range ((pullback.snd j v) ∘ h.isoPullback.hom))
  rw [he.range_comp]
  exact hh

end M9Native.EtaleDensePullback

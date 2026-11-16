module

public import M9StacksIntegration.ProperSmoothLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! The actual largest proper smooth base open commutes with flat base
change. Every source point of the original fibre is lifted through the
cartesian square; the native smooth-locus base-change theorem then
reflects smoothness at that point. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.ProperSmoothLocusBaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {a : X' ⟶ X} {b : Y' ⟶ Y}
  [LocallyOfFinitePresentation f] [IsProper f]
  [LocallyOfFinitePresentation f'] [IsProper f']

/-- Equality of the genuine proper smooth opens, including reflection
from the entire base-changed fibre to every original fibre point. -/
theorem goodOpen_eq_preimage (sq : IsPullback a f' f b)
    (hflat : Flat f ∨ Flat b) :
    ProperSmoothLocus.goodOpen f' = b ⁻¹ᵁ ProperSmoothLocus.goodOpen f := by
  have hs := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback sq hflat
  ext y'
  change y' ∈ ProperSmoothLocus.goodOpen f' ↔ b y' ∈ ProperSmoothLocus.goodOpen f
  rw [ProperSmoothLocus.mem_goodOpen_iff, ProperSmoothLocus.mem_goodOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨x', hax, hfx⟩ := Scheme.exists_preimage_of_isPullback sq x y' hx
    have hm := h x' hfx
    rw [hs] at hm
    change a x' ∈ f.smoothLocus at hm
    simpa only [hax] using hm
  · intro h x' hx'
    rw [hs]
    change a x' ∈ f.smoothLocus
    apply h (a x')
    have hw := congrArg (fun k : X' ⟶ Y => k x') sq.w
    simpa only [Scheme.Hom.comp_apply, hx'] using hw

end M9Native.ProperSmoothLocusBaseChange

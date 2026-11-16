module

public import M9StacksIntegration.LineTupleZeroScheme
public import M9StacksIntegration.LineFamilyCapPower
public import Mathlib.Tactic.NoncommRing

/-! The actual fourth Chern cap of four copies of an original line is
its actual fourth first-Chern cap power, on every original Chow class.
The full Chern formula comes from proved native split rows and Whitney;
only finite graded-ring coefficient extraction is performed here. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
universe u v
namespace M9Native.LineTupleTopChern
open ChowCapWords GradedLineCapSubring LineTupleZeroScheme

/-- Finite coefficient extraction in the genuine, possibly
noncommutative, graded-cap ring. -/
theorem fourthComponent_one_add_pow {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]
    (x : GradedCapFamily G) (hx : x.IsHomogeneous 1) :
    homComponent 4 ((1+x)^4) = x^4 := by
  have he : (1+x)^4 = 1 + 4 • x + 6 • x^2 + 4 • x^3 + x^4 := by
    noncomm_ring
  rw [he]
  simp only [map_add, map_nsmul,
    GradedCapFamily.IsHomogeneous.one.homComponent_of_ne (by decide : 4 ≠ 0),
    hx.homComponent_of_ne (by decide : 4 ≠ 1),
    (hx.pow 2).homComponent_of_ne (by decide : 4 ≠ 2),
    (hx.pow 3).homComponent_of_ne (by decide : 4 ≠ 3),
    (hx.pow 4).homComponent_self, nsmul_zero, add_zero, zero_add]

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (L : InvertibleLine X)

theorem fourthComponent_tupleBundle :
    homComponent 4 (chernFamily C q (tupleBundle L 4) 4) = lineFamily C q L ^ 4 := by
  rw [chernFamily_tupleBundle L 4 C q]
  exact fourthComponent_one_add_pow _ (lineFamily_homogeneous C q L)

/-- On every Chow class this is the original native c4 cap and the
original native c1 cap power, with the actual output grade. -/
theorem topCap_eq_four_line_caps (k : ℤ) (α : chowGroup C q k) :
    chernCap C 4 q (tupleBundle L 4) k (Fin.last 4) α =
      capPow C q (lineCap C q L) 4 k (k-4) (by omega) α := by
  have h := congrArg (fun a : GradedCapFamily (chowGroup C q) => a k 4 α)
    (fourthComponent_tupleBundle C q L)
  rw [homComponent_apply_self,
    chernFamily_apply_of_le C q (tupleBundle L 4) 4 k (le_refl 4)] at h
  exact h.trans (LineFamilyCapPower.lineFamily_pow_apply C q L 4 k α)

end M9Native.LineTupleTopChern

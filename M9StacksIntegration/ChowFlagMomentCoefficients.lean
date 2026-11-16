module

public import M9StacksIntegration.ChowLineFamilyComparison
public import M9StacksIntegration.ChowVirtualDuality
public import Mathlib.Tactic.NoncommRing

/-!
# Ordered coefficient extraction for genuine line factors

The generic identities use the actual native graded cap ring and its
homogeneous components. They require no ambient commutativity. The
actual signed rank-one Chern family is identified with one minus the
same original geometric line-cap family by genuine native duality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Finset Stacks.Chow
open Stacks.Chow.GenuineChern
universe u v
namespace M9Native.ChowFlagMomentCoefficients

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- A homogeneous left factor selects its unique coefficient in the
native ordered convolution. No commutativity is used. -/
theorem homComponent_mul_of_homogeneous_left (x c : GradedCapFamily G)
    {i : ℕ} (hx : x.IsHomogeneous i) (m : ℕ) (him : i ≤ m) :
    homComponent m (x*c) = x * homComponent (m-i) c := by
  rw [homComponent_mul, Finset.sum_eq_single (m-i)]
  · rw [show m-(m-i)=i by omega, hx.homComponent_self]
  · intro j hj hji
    have hjm : j ≤ m := mem_range_succ_iff.mp hj
    rw [hx.homComponent_of_ne (by omega : m-j ≠ i), zero_mul]
  · intro hj
    exact (hj (mem_range.mpr (by omega))).elim

/-- One genuine degree-one factor has the literal ordered two-term
coefficient expansion. -/
theorem homComponent_one_sub_mul (x c : GradedCapFamily G)
    (hx : x.IsHomogeneous 1) (m : ℕ) (hm : 1 ≤ m) :
    homComponent m ((1-x)*c) =
      homComponent m c - x * homComponent (m-1) c := by
  rw [sub_mul, one_mul, map_sub,
    homComponent_mul_of_homogeneous_left x c hx m hm]

/-- Two original degree-one factors have the literal four ordered
terms in the coefficient. The order x*y is retained. -/
theorem homComponent_two_one_sub_mul (x y c : GradedCapFamily G)
    (hx : x.IsHomogeneous 1) (hy : y.IsHomogeneous 1) (m : ℕ) (hm : 2 ≤ m) :
    homComponent m (((1-x)*(1-y))*c) =
      homComponent m c - x * homComponent (m-1) c -
        y * homComponent (m-1) c + (x*y) * homComponent (m-2) c := by
  have hraw : ((1-x)*(1-y))*c = c - x*c - y*c + (x*y)*c := by noncomm_ring
  rw [hraw, map_add, map_sub, map_sub,
    homComponent_mul_of_homogeneous_left x c hx m (by omega),
    homComponent_mul_of_homogeneous_left y c hy m (by omega),
    homComponent_mul_of_homogeneous_left (x*y) c (hx.mul hy) m hm]

end Generic

/-- The signed actual rank-one Chern family is one minus the actual
line-cap family of the SAME original invertible sheaf. -/
theorem signed_chernFamily_line (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (L : ChowCapWords.InvertibleLine X) :
    letI := L.2
    letI := @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L.1 L.2
    capFamilySignScale (chernFamily C q L.1 1) =
      1 - GradedLineCapSubring.lineFamily C q L := by
  letI := L.2
  letI := @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L.1 L.2
  have hd := ChowVirtualDuality.actual_dualFamily C q L.1 1
  have hl := ChowLineFamilyComparison.chernFamily_dualLine C q L
  exact hd.symm.trans hl

end M9Native.ChowFlagMomentCoefficients

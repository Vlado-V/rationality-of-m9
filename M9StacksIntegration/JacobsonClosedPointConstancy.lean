module

public import Mathlib.Topology.JacobsonSpace

@[expose] public section

/-! A natural-valued upper semicontinuous function on a Jacobson space is
determined to be constant by its actual values at every closed point.
-/

namespace M9Native.JacobsonClosedPointConstancy

universe u

open TopologicalSpace

variable {Y : Type u} [TopologicalSpace Y] [JacobsonSpace Y]

/-- Every nonempty Jacobson space has an actual closed point. -/
theorem exists_closed_point (x : Y) : ∃ y : Y, IsClosed ({y} : Set Y) := by
  obtain ⟨y, -, hy⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set Y)) ⟨x, Set.mem_univ x⟩ isOpen_univ.isLocallyClosed
  exact ⟨y, hy⟩

/-- Genuine upper semicontinuity and the closed-point values force equality
at every point.  No rank condition at nonclosed points is an input. -/
theorem nat_eq_of_closed_points (q : Y → ℕ)
    (hopen : ∀ n : ℕ, IsOpen {x : Y | q x ≤ n}) (r : ℕ)
    (hclosed : ∀ x : Y, IsClosed ({x} : Set Y) → q x = r) :
    ∀ x : Y, q x = r := by
  intro x
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (Z := {y : Y | q y ≤ q x}) ⟨x, show q x ≤ q x from le_rfl⟩
    (hopen (q x)).isLocallyClosed
  have hlower : r ≤ q x := by
    change q y ≤ q x at hy
    rwa [hclosed y hyc] at hy
  have hupper : q x ≤ r := by
    by_contra hx
    have hx' : r < q x := Nat.lt_of_not_ge hx
    have hZ : IsClosed {y : Y | r < q y} := by
      simpa only [Set.compl_ofPred, not_le] using (hopen r).isClosed_compl
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (Z := {y : Y | r < q y}) ⟨x, hx'⟩ hZ.isLocallyClosed
    change r < q z at hz
    rw [hclosed z hzc] at hz
    exact (Nat.lt_irrefl r) hz
  exact le_antisymm hupper hlower

end M9Native.JacobsonClosedPointConstancy

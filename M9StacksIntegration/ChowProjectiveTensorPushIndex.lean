module

public import Mathlib.Algebra.BigOperators.Fin
public import Lean.Elab.Tactic.Omega

/-! The finite index shift in the projective tensor-push convolution.
Only an additive commutative monoid and the displayed low-index zero
condition are used; no geometric Chern or rank-support fact is assumed. -/

@[expose] public section

open scoped BigOperators

namespace M9Native.ChowProjectiveTensorPushIndex

variable {M : Type*} [AddCommMonoid M]

/-- The actual filtered-domain bijection is `j ↦ a+j-n`, with inverse
`m ↦ n+m-a`; the omitted target indices vanish by the explicit hypothesis. -/
theorem range_reindex (r a n b : ℕ) (hab : r + a = n + b) (f : ℕ → M)
    (hzero : ∀ m, m ≤ b → n + m < a → f m = 0) :
    (∑ j ∈ Finset.range (r + 1), if n ≤ a + j then f (a + j - n) else 0) =
      ∑ m ∈ Finset.range (b + 1), f m := by
  let J := (Finset.range (r + 1)).filter (fun j => n ≤ a + j)
  let T := (Finset.range (b + 1)).filter (fun m => a ≤ n + m)
  have hbij : (∑ j ∈ J, f (a + j - n)) = ∑ m ∈ T, f m := by
    refine Finset.sum_bij (fun j _ => a + j - n) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨hjr, hna⟩ := Finset.mem_filter.mp hj
      have hjr' := Finset.mem_range.mp hjr
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · omega
    · intro j hj k hk heq
      obtain ⟨_, hjn⟩ := Finset.mem_filter.mp hj
      obtain ⟨_, hkn⟩ := Finset.mem_filter.mp hk
      omega
    · intro m hm
      obtain ⟨hmb, ham⟩ := Finset.mem_filter.mp hm
      have hmb' := Finset.mem_range.mp hmb
      refine ⟨n + m - a, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_range.mpr
          omega
        · omega
      · omega
    · intro j hj
      rfl
  calc
    (∑ j ∈ Finset.range (r + 1), if n ≤ a + j then f (a + j - n) else 0) =
        ∑ j ∈ J, f (a + j - n) := (Finset.sum_filter _ _).symm
    _ = ∑ m ∈ T, f m := hbij
    _ = ∑ m ∈ Finset.range (b + 1), f m := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro m hm hmt
      have hmb := Finset.mem_range.mp hm
      have hlow : n + m < a := by
        have hn : ¬ a ≤ n + m := by
          intro h
          exact hmt (Finset.mem_filter.mpr ⟨hm, h⟩)
        omega
      exact hzero m (by omega) hlow

/-- The same literal identity with the source indexed by its finite rank. -/
theorem fin_reindex_range (r a n b : ℕ) (hab : r + a = n + b) (f : ℕ → M)
    (hzero : ∀ m, m ≤ b → n + m < a → f m = 0) :
    (∑ j : Fin (r + 1), if n ≤ a + j.val then f (a + j.val - n) else 0) =
      ∑ m ∈ Finset.range (b + 1), f m := by
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if n ≤ a + j then f (a + j - n) else 0) (r + 1)).trans
      (range_reindex r a n b hab f hzero)

/-- Both finite-rank index sets use the same proved filtered bijection. -/
theorem fin_reindex (r a n b : ℕ) (hab : r + a = n + b) (f : ℕ → M)
    (hzero : ∀ m, m ≤ b → n + m < a → f m = 0) :
    (∑ j : Fin (r + 1), if n ≤ a + j.val then f (a + j.val - n) else 0) =
      ∑ m : Fin (b + 1), f m.val := by
  exact (fin_reindex_range r a n b hab f hzero).trans
    (Fin.sum_univ_eq_sum_range f (b + 1)).symm

end M9Native.ChowProjectiveTensorPushIndex

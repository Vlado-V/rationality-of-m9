module

public import M9StacksIntegration.CurvePowerTopPower

/-!
# The finite moving-graph factors and the root-shift list

This identifies the literal finite list used by the root calculation
with nine copies of the normalization class and the nine moving-graph
quotient classes, after their genuine numerical diagonal relations have
been established. It asserts no bundle or Chern-class comparison.
-/

@[expose] public section

open scoped BigOperators

namespace M9Native.CurvePowerFiltrationRoots

open CurvePowerRootSums CurvePowerTopPower

variable {R : Type*} [CommRing R]

def pointSum (p : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => pointSum p n + p n

theorem pointSum_eq_sum (p : ℕ → R) (n : ℕ) : pointSum p n = ∑ i ∈ Finset.range n, p i := by
  induction n with
  | zero => simp [pointSum]
  | succ n ih => rw [pointSum, Finset.sum_range_succ, ih]

def factor (p b : ℕ → R) (ambient j : ℕ) : R :=
  (j : R) * p j + b j + pointSum p (j + 1) - pointSum p ambient

theorem factor_last (p b : ℕ → R) (n : ℕ) :
    factor p b (n + 1) n = (n : R) * p n + b n := by
  simp only [factor, add_sub_cancel_right]

theorem factor_succ (p b : ℕ → R) (n j : ℕ) :
    factor p b (n + 1) j = factor p b n j - p n := by
  simp only [factor, pointSum]
  ring

theorem roots_eq_filtration_factors (g : ℕ) (p b : ℕ → R) (n : ℕ) :
    roots g p b n =
      ((List.range n).reverse.map (factor p b n)) ++ List.replicate g (-pointSum p n) := by
  induction n with
  | zero => simp [roots, pointSum]
  | succ n ih =>
      rw [roots, nextRoots, ih]
      have hf : (fun a => a - p n) ∘ factor p b n = factor p b (n + 1) := by
        funext j
        exact (factor_succ p b n j).symm
      have hp : -pointSum p n - p n = -pointSum p (n + 1) := by
        simp only [pointSum]
        ring
      simp only [List.map_append, List.map_map, List.map_replicate, List.range_succ,
        List.reverse_append, List.reverse_singleton, List.map_cons,
        List.cons_append, List.nil_append, factor_last, hf, hp]

def graphQuotient (p : ℕ → R) (δ : ℕ → ℕ → R) (ambient j : ℕ) : R :=
  -pointSum p ambient + 17 * p j + ∑ a ∈ Finset.range (j + 1), δ j a

theorem graphQuotient_eq_factor (p : ℕ → R) (β δ : ℕ → ℕ → R) (ambient j : ℕ)
    (hself : δ j j = -16 * p j)
    (hother : ∀ i, i < j → δ j i = β i j + p i + p j) :
    graphQuotient p δ ambient j = factor p (boundary β) ambient j := by
  have hs : (∑ i ∈ Finset.range j, δ j i) =
      ∑ i ∈ Finset.range j, (β i j + p i + p j) :=
    Finset.sum_congr rfl (fun i hi => hother i (Finset.mem_range.mp hi))
  rw [graphQuotient, Finset.sum_range_succ, hself, hs]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [factor, pointSum, pointSum_eq_sum, boundary]
  ring

theorem roots_nine_eq_actual_factor_shape (p : ℕ → R) (β δ : ℕ → ℕ → R)
    (hself : ∀ j, j < 9 → δ j j = -16 * p j)
    (hother : ∀ i j, i < j → j < 9 → δ j i = β i j + p i + p j) :
    roots 9 p (boundary β) 9 =
      ((List.range 9).reverse.map (graphQuotient p δ 9)) ++ List.replicate 9 (-pointSum p 9) := by
  rw [roots_eq_filtration_factors]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj9 : j < 9 := List.mem_range.mp (List.mem_reverse.mp hj)
  exact (graphQuotient_eq_factor p β δ 9 j (hself j hj9)
    (fun i hij => hother i j hij hj9)).symm

end M9Native.CurvePowerFiltrationRoots

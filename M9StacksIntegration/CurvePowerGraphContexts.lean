module

public import M9StacksIntegration.CurvePowerGraphInduction
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Bitwise

/-!
# Rebase local diagonal relations in a partition context

The ambient curve power and the original divisor word stay fixed.
Only the current unmarked blocks change. A local context assigns the
five labels of the frozen certificate to actual block masks and adds
all untouched blocks as spectators. Zero labels represent absent blocks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.CurvePowerGraphContexts

open CurvePowerGraphLocal CurvePowerGraphInduction

theorem insertBlock_eq_orderedInsert (a : ℕ) (s : State) :
    insertBlock a s = List.orderedInsert (· ≤ ·) a s := by
  induction s with
  | nil => simp only [insertBlock, List.orderedInsert_nil]
  | cons b s ih => simp only [insertBlock, List.orderedInsert_cons, ih]

theorem canonical_eq_insertionSort (s : State) :
    canonical s = List.insertionSort (· ≤ ·) s := by
  induction s with
  | nil => simp only [canonical, List.insertionSort_nil]
  | cons a s ih =>
      rw [canonical, List.insertionSort_cons, ih, insertBlock_eq_orderedInsert]

theorem canonical_eq_of_perm {s t : State} (h : s.Perm t) : canonical s = canonical t := by
  rw [canonical_eq_insertionSort, canonical_eq_insertionSort]
  exact List.Perm.eq_of_pairwise' (List.pairwise_insertionSort (· ≤ ·) s)
    (List.pairwise_insertionSort (· ≤ ·) t)
    (((List.perm_insertionSort (· ≤ ·) s).trans h).trans
      (List.perm_insertionSort (· ≤ ·) t).symm)

theorem canonical_perm (s : State) : (canonical s).Perm s := by
  rw [canonical_eq_insertionSort]
  exact List.perm_insertionSort (· ≤ ·) s

structure Context where
  label : Fin 5 → ℕ
  spectator : State

def liftMask (f : Fin 5 → ℕ) (b : ℕ) : ℕ :=
  (if b.testBit 0 then f 0 else 0) |||
  (if b.testBit 1 then f 1 else 0) |||
  (if b.testBit 2 then f 2 else 0) |||
  (if b.testBit 3 then f 3 else 0) |||
  (if b.testBit 4 then f 4 else 0)

def transport (ctx : Context) (s : State) : State :=
  canonical ((s.map (liftMask ctx.label)).filter (· ≠ 0) ++ ctx.spectator)

def pin (ctx : Context) (i : Fin 5) : Context :=
  { ctx with label := Function.update ctx.label i 0 }

def merge (ctx : Context) (i j : Fin 5) : Context :=
  { ctx with label := (Function.update
      (Function.update ctx.label i (ctx.label i ||| ctx.label j)) j 0) }

theorem transport_canonical (ctx : Context) (s : State) :
    transport ctx (canonical s) = transport ctx s := by
  apply canonical_eq_of_perm
  exact (((canonical_perm s).map (liftMask ctx.label)).filter (· ≠ 0)).append_right _

theorem lor_left_comm (a b c : ℕ) : a ||| (b ||| c) = b ||| (a ||| c) := by
  rw [← Nat.lor_assoc, Nat.lor_comm a b, Nat.lor_assoc]

theorem label_swap_zero_one (ctx : Context) (a : ℕ) :
    ctx.label 1 ||| (ctx.label 0 ||| a) = ctx.label 0 ||| (ctx.label 1 ||| a) :=
  lor_left_comm _ _ _

theorem label_swap_zero_one_prop (ctx : Context) (P : Prop) :
    (ctx.label 1 ≠ 0 ∨ ctx.label 0 ≠ 0 ∨ P) ↔
      (ctx.label 0 ≠ 0 ∨ ctx.label 1 ≠ 0 ∨ P) := or_left_comm

variable {M : Type*} [AddCommGroup M]

theorem realization_nil (t : ℤ) (F : State → M) : realization t F [] = 0 := by
  simp [realization, encoded]

theorem realization_cons (t : ℤ) (F : State → M) (s : State) (a : Coefficient)
    (c : Combination) :
    realization t F ((s, a) :: c) = (a.1 + a.2 * t) • F s + realization t F c := by
  change (Finsupp.single s a + encoded c).sum (fun s a => (a.1 + a.2 * t) • F s) = _
  rw [Finsupp.sum_add_index]
  · rw [Finsupp.sum_single_index]
    · rfl
    · simp
  · intro s
    simp
  · intro s hs a b
    simp only [Prod.fst_add, Prod.snd_add, add_mul, add_smul]
    abel

theorem realization_embed (t : ℤ) (F : State → M) (c : SourceCombination) :
    realization t F (embed c) = (c.map fun (s, a) => a • F s).sum := by
  induction c with
  | nil => exact realization_nil t F
  | cons a c ih =>
      rcases a with ⟨s, a⟩
      simp only [embed, List.map_cons, realization_cons, zero_mul, add_zero,
        List.sum_cons]
      exact congrArg ((a • F s) + ·) ih

theorem localGamma_explicit : localGamma =
    [([7, 8, 16], 1), ([3, 8, 16], -1), ([5, 8, 16], -1),
     ([6, 8, 16], -1), ([4, 8, 16], 1), ([2, 8, 16], 1), ([1, 8, 16], 1)] := by
  decide

theorem pointExpected_three : pointExpected 3 = embed
    [([7, 16], 1), ([3, 16], -1), ([5, 16], -1),
     ([6, 16], -1), ([4, 16], 1), ([2, 16], 1), ([1, 16], 1)] := by
  decide

theorem pointExpected_four : pointExpected 4 = embed
    [([7, 8], 1), ([3, 8], -1), ([5, 8], -1),
     ([6, 8], -1), ([4, 8], 1), ([2, 8], 1), ([1, 8], 1)] := by
  decide

theorem point_rebase (t : ℤ) (F : State → M) (ctx : Context) (i : Fin 5)
    (hi : 3 ≤ i.val) :
    realization t (F ∘ transport ctx) (pointExpected i.val) =
      realization t (F ∘ transport (pin ctx i)) (embed localGamma) := by
  fin_cases i <;> norm_num at hi
  all_goals
    simp only [pointExpected_three, pointExpected_four, localGamma_explicit]
    rw [realization_embed, realization_embed]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Function.comp_apply]
    simp [transport, pin, liftMask, Nat.testBit, Nat.shiftRight_eq_div_pow, List.filter_cons]

theorem diagonal_rebase_special_other (t : ℤ) (F : State → M) (ctx : Context)
    (i j : Fin 5) (hi : i.val < 3) (hj : 3 ≤ j.val) :
    realization t (F ∘ transport ctx) (diagonalExpected i.val j.val) =
      realization t (F ∘ transport (merge ctx i j)) (embed localGamma) := by
  fin_cases i <;> fin_cases j <;> simp at hi hj
  all_goals
    simp only [diagonalExpected, enlargeSpecial]
    norm_num
    simp only [realization_embed, localGamma, gamma, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Function.comp_apply, transport_canonical]
    simp [transport, merge, liftMask, bit, Nat.testBit, Nat.shiftRight_eq_div_pow,
      List.filter_cons, Nat.lor_assoc, lor_left_comm, Nat.lor_comm]
  all_goals simp only [label_swap_zero_one, label_swap_zero_one_prop]

theorem point_kills_special (t : ℤ) (F : State → M) (i : Fin 5) (hi : i.val < 3) :
    realization t F (pointExpected i.val) = 0 := by
  simp only [pointExpected, ite_eq_left hi, realization_nil]

theorem diagonal_kills_special_pair (t : ℤ) (F : State → M) (i j : Fin 5)
    (hi : i.val < 3) (hj : j.val < 3) :
    realization t F (diagonalExpected i.val j.val) = 0 := by
  by_cases hij : i.val = j.val
  · simp only [diagonalExpected, ite_eq_left hij, pointExpected, ite_eq_left hi,
      List.map_nil, realization_nil]
  · simp only [diagonalExpected, ite_eq_right hij, ite_eq_left hi, ite_eq_left hj, realization_nil]

theorem diagonal_rebase_other_special (t : ℤ) (F : State → M) (ctx : Context)
    (i j : Fin 5) (hi : 3 ≤ i.val) (hj : j.val < 3) :
    realization t (F ∘ transport ctx) (diagonalExpected i.val j.val) =
      realization t (F ∘ transport (merge ctx j i)) (embed localGamma) := by
  have hne : i.val ≠ j.val := by omega
  have hne' : j.val ≠ i.val := Ne.symm hne
  have he : diagonalExpected i.val j.val = diagonalExpected j.val i.val := by
    simp only [diagonalExpected, ite_eq_right hne, ite_eq_right hne',
      ite_eq_right (not_lt.mpr hi), ite_eq_left hj]
  rw [he]
  exact diagonal_rebase_special_other t F ctx j i hj hi

theorem diagonal_rebase_other_pair (t : ℤ) (F : State → M) (ctx : Context)
    (i j : Fin 5) (hi : 3 ≤ i.val) (hj : 3 ≤ j.val) (hne : i ≠ j) :
    realization t (F ∘ transport ctx) (diagonalExpected i.val j.val) =
      realization t (F ∘ transport (merge ctx i j)) (embed localGamma) := by
  fin_cases i <;> fin_cases j <;> simp at hi hj hne
  all_goals
    simp only [diagonalExpected]
    norm_num
    simp only [realization_embed, localGamma, gamma, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Function.comp_apply, transport_canonical]
    simp [transport, merge, liftMask, bit, Nat.testBit, Nat.shiftRight_eq_div_pow,
      List.filter_cons, Nat.lor_assoc, Nat.lor_comm]

theorem realization_self_embed (t : ℤ) (F : State → M) (c : SourceCombination) :
    realization t F ((embed c).map fun (s, a) => (s, (0, a.1))) =
      t • realization t F (embed c) := by
  induction c with
  | nil => simp only [embed, List.map_nil, realization_nil, smul_zero]
  | cons a c ih =>
      rcases a with ⟨s, a⟩
      change realization t F ((s, (0, a)) ::
          (embed c).map (fun (s, a) => (s, (0, a.1)))) =
        t • realization t F ((s, (a, 0)) :: embed c)
      rw [realization_cons, realization_cons, ih]
      simp only [zero_mul, add_zero, zero_add, smul_add, smul_smul]
      rw [mul_comm a t]

theorem diagonal_rebase_self_other (t : ℤ) (F : State → M) (ctx : Context)
    (i : Fin 5) (hi : 3 ≤ i.val) :
    realization t (F ∘ transport ctx) (diagonalExpected i.val i.val) =
      t • realization t (F ∘ transport (pin ctx i)) (embed localGamma) := by
  obtain ⟨c, hc⟩ : ∃ c, pointExpected i.val = embed c :=
    ⟨gamma 1 2 4 ([8, 16].erase (bit i.val)), by
      simp only [pointExpected, ite_eq_right (not_lt.mpr hi)]⟩
  have he : diagonalExpected i.val i.val =
      (pointExpected i.val).map (fun (s, a) => (s, (0, a.1))) := by
    simp [diagonalExpected]
  rw [he, hc, realization_self_embed, ← hc, point_rebase t F ctx i hi]

/-- The descendant context is computed from the local operation. It
contains no numerical vanishing assertion. -/
def rebase (t : ℤ) (ctx : Context) : LocalKind → Option (ℤ × Context)
  | .point i =>
      if i.val < 3 then none else some (1, pin ctx i)
  | .diagonal i j =>
      if i = j then
        if i.val < 3 then none else some (t, pin ctx i)
      else if i.val < 3 then
        if j.val < 3 then none else some (1, merge ctx i j)
      else if j.val < 3 then some (1, merge ctx j i)
      else some (1, merge ctx i j)

def rebasedValue (t : ℤ) (F : State → M) : Option (ℤ × Context) → M
  | none => 0
  | some (weight, ctx) =>
      weight • realization t (F ∘ transport ctx) (embed localGamma)

/-- Every expected local relation is either zero or an explicitly
weighted modified diagonal in its computed descendant context. -/
theorem expected_rebase (t : ℤ) (F : State → M) (ctx : Context) (kind : LocalKind) :
    realization t (F ∘ transport ctx) (expected kind) =
      rebasedValue t F (rebase t ctx kind) := by
  cases kind with
  | point i =>
      by_cases hi : i.val < 3
      · simpa only [expected, rebase, ite_eq_left hi, rebasedValue] using
          point_kills_special t (F ∘ transport ctx) i hi
      · simpa only [expected, rebase, ite_eq_right hi, rebasedValue, one_smul] using
          point_rebase t F ctx i (Nat.le_of_not_gt hi)
  | diagonal i j =>
      by_cases hij : i = j
      · subst j
        by_cases hi : i.val < 3
        · simpa only [expected, rebase, ite_eq_left rfl, ite_eq_left hi, ite_true,
              rebasedValue] using
            diagonal_kills_special_pair t (F ∘ transport ctx) i i hi hi
        · simpa only [expected, rebase, ite_eq_left rfl, ite_eq_right hi, ite_true,
              rebasedValue] using
            diagonal_rebase_self_other t F ctx i (Nat.le_of_not_gt hi)
      · by_cases hi : i.val < 3
        · by_cases hj : j.val < 3
          · simpa only [expected, rebase, ite_eq_right hij, ite_eq_left hi,
                ite_eq_left hj, rebasedValue] using
              diagonal_kills_special_pair t (F ∘ transport ctx) i j hi hj
          · simpa only [expected, rebase, ite_eq_right hij, ite_eq_left hi,
                ite_eq_right hj, rebasedValue, one_smul] using
              diagonal_rebase_special_other t F ctx i j hi (Nat.le_of_not_gt hj)
        · by_cases hj : j.val < 3
          · simpa only [expected, rebase, ite_eq_right hij, ite_eq_right hi,
                ite_eq_left hj, rebasedValue, one_smul] using
              diagonal_rebase_other_special t F ctx i j (Nat.le_of_not_gt hi) hj
          · simpa only [expected, rebase, ite_eq_right hij, ite_eq_right hi,
                ite_eq_right hj, rebasedValue, one_smul] using
              diagonal_rebase_other_pair t F ctx i j
                (Nat.le_of_not_gt hi) (Nat.le_of_not_gt hj) hij

end M9Native.CurvePowerGraphContexts

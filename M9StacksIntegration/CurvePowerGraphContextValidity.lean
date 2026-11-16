module

public import M9StacksIntegration.CurvePowerGraphContexts

/-!
# Nonempty distinguished blocks under local restriction

A context retains three genuine distinguished blocks. The two outside
labels may be zero when absent. Every nonzero descendant computed by
restriction still retains these distinguished blocks, and every term
of its modified diagonal has positive source dimension.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphContextValidity

open CurvePowerGraphLocal CurvePowerGraphInduction CurvePowerGraphContexts

def Valid (ctx : Context) : Prop :=
  ctx.label 0 ≠ 0 ∧ ctx.label 1 ≠ 0 ∧ ctx.label 2 ≠ 0

theorem valid_pin (ctx : Context) (hctx : Valid ctx) (i : Fin 5) (hi : 3 ≤ i.val) :
    Valid (pin ctx i) := by
  fin_cases i <;> simp at hi
  all_goals simpa [Valid, pin] using hctx

theorem valid_merge (ctx : Context) (hctx : Valid ctx) (i j : Fin 5)
    (hj : 3 ≤ j.val) : Valid (merge ctx i j) := by
  rcases hctx with ⟨h0, h1, h2⟩
  fin_cases i <;> fin_cases j <;> simp at hj
  all_goals simp [Valid, merge, h0, h1, h2]

theorem valid_rebase (t : ℤ) (ctx : Context) (hctx : Valid ctx) (kind : LocalKind)
    (weight : ℤ) (child : Context) (h : rebase t ctx kind = some (weight, child)) :
    Valid child := by
  cases kind with
  | point i =>
      by_cases hi : i.val < 3
      · simp only [rebase, ite_eq_left hi] at h
        contradiction
      · simp only [rebase, ite_eq_right hi, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact valid_pin ctx hctx i (Nat.le_of_not_gt hi)
  | diagonal i j =>
      by_cases hij : i = j
      · subst j
        by_cases hi : i.val < 3
        · simp [rebase, hi] at h
        · have he : child = pin ctx i := by simpa [rebase, hi] using (congrArg (Option.map Prod.snd) h).symm
          rw [he]
          exact valid_pin ctx hctx i (Nat.le_of_not_gt hi)
      · by_cases hi : i.val < 3
        · by_cases hj : j.val < 3
          · simp [rebase, hij, hi, hj] at h
          · have he : child = merge ctx i j := by
              simpa [rebase, hij, hi, hj] using (congrArg (Option.map Prod.snd) h).symm
            rw [he]
            exact valid_merge ctx hctx i j (Nat.le_of_not_gt hj)
        · by_cases hj : j.val < 3
          · have he : child = merge ctx j i := by
              simpa [rebase, hij, hi, hj] using (congrArg (Option.map Prod.snd) h).symm
            rw [he]
            exact valid_merge ctx hctx j i (Nat.le_of_not_gt hi)
          · have he : child = merge ctx i j := by
              simpa [rebase, hij, hi, hj] using (congrArg (Option.map Prod.snd) h).symm
            rw [he]
            exact valid_merge ctx hctx i j (Nat.le_of_not_gt hj)

theorem canonical_length (s : State) : (canonical s).length = s.length :=
  (canonical_perm s).length_eq

theorem transport_positive_of_nonzero (ctx : Context) (s : State) (b : ℕ)
    (hb : b ∈ s) (hn : liftMask ctx.label b ≠ 0) :
    0 < (transport ctx s).length := by
  rw [transport, canonical_length]
  have hm : liftMask ctx.label b ∈ (s.map (liftMask ctx.label)).filter (· ≠ 0) := by
    simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
    exact ⟨⟨b, hb, rfl⟩, hn⟩
  have hp : 0 < ((s.map (liftMask ctx.label)).filter (· ≠ 0)).length :=
    List.length_pos_of_mem hm
  simpa only [List.length_append] using hp.trans_le (Nat.le_add_right _ _)

theorem transport_localGamma_positive (ctx : Context) (hctx : Valid ctx) (s : State)
    (hs : s ∈ keys (embed localGamma)) : 0 < (transport ctx s).length := by
  rcases hctx with ⟨h0, h1, h2⟩
  have hstates : s = [7, 8, 16] ∨ s = [3, 8, 16] ∨ s = [5, 8, 16] ∨
      s = [6, 8, 16] ∨ s = [4, 8, 16] ∨ s = [2, 8, 16] ∨ s = [1, 8, 16] := by
    simpa only [localGamma_explicit, keys, embed, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, eq_comm] using hs
  rcases hstates with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply transport_positive_of_nonzero ctx _ _ List.mem_cons_self
    simp [liftMask, Nat.testBit, Nat.shiftRight_eq_div_pow, h0, h1, h2]

end M9Native.CurvePowerGraphContextValidity

module

public import M9StacksIntegration.CurvePowerGraphInduction

/-!
# Restriction induction from the actual modified-diagonal base case

This form permits genuine partition frames carrying separation data.
It requires only the actual empty-word modified-diagonal value, rather
than values on states outside the support of the local certificate.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphKeyInduction

open CurvePowerGraphLocal CurvePowerGraphInduction

variable {Frame Factor M : Type*} [AddCommGroup M]

theorem gammaValue_zero_of_nil_and_restrictions (t : ℤ) (F : Functional Frame Factor M)
    (hbase : ∀ frame, gammaValue t F frame [] = 0)
    (step : ∀ frame factor tail, RestrictionStep t F frame factor tail)
    (frame : Frame) (word : List Factor) : gammaValue t F frame word = 0 := by
  have H : ∀ n : ℕ, ∀ frame word, word.length ≤ n → gammaValue t F frame word = 0 := by
    intro n
    induction n with
    | zero =>
        intro frame word hw
        cases word with
        | nil => exact hbase frame
        | cons factor tail => simp at hw
    | succ n ih =>
        intro frame word hw
        cases word with
        | nil => exact hbase frame
        | cons factor tail =>
            let r := step frame factor tail
            have ht : tail.length ≤ n := by simpa using hw
            calc
              gammaValue t F frame (factor :: tail) =
                  realization t r.afterRestriction (action r.kind) := r.restriction_eq
              _ = realization t r.afterRestriction (expected r.kind) :=
                local_realization t r.afterRestriction r.kind
              _ = descendantValue t F r.descendant := r.rebase_eq
              _ = 0 := by
                cases hd : r.descendant with
                | none => rfl
                | some d =>
                    change d.weight • gammaValue t F d.frame d.word = 0
                    rw [ih d.frame d.word ((r.length_le d hd).trans ht), smul_zero]
  exact H word.length frame word le_rfl

end M9Native.CurvePowerGraphKeyInduction

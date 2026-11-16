module

public import M9StacksIntegration.CurvePowerGraphLocal

/-!
# Induction from local restrictions to modified-diagonal vanishing

The functional is arbitrary. Its restriction presentation records the
actual point/diagonal restriction equality, the rebase equality after
restriction, and the decrease in the number of remaining factors. The
local seven-term equality is proved by the imported kernel certificates.

There is no geometric instance asserted in this file: the actual native
curve-power functional and its restriction presentation are constructed
separately. In particular, no numerical radical or Chern identity is an
input field.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphInduction

open CurvePowerGraphLocal

variable {M : Type*} [AddCommGroup M]

inductive LocalKind where
  | point (i : Fin 5)
  | diagonal (i j : Fin 5)

def action : LocalKind → Combination
  | .point i => pointAction i.val localGamma
  | .diagonal i j => diagonalAction i.val j.val localGamma

def expected : LocalKind → Combination
  | .point i => pointExpected i.val
  | .diagonal i j => diagonalExpected i.val j.val

theorem local_realization (t : ℤ) (F : State → M) (kind : LocalKind) :
    realization t F (action kind) = realization t F (expected kind) := by
  cases kind with
  | point i => exact point_realization_eq t F i
  | diagonal i j => exact diagonal_realization_eq t F i j

theorem realization_zero_of_keys (t : ℤ) (F : State → M) (c : Combination)
    (hF : ∀ s ∈ keys c, F s = 0) : realization t F c = 0 := by
  unfold realization
  apply Finset.sum_eq_zero
  intro s hs
  have hn : encoded c s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hk : s ∈ keys c := by
    by_contra h
    apply hn
    rw [encoded_apply, coefficient_zero_of_not_key c s h]
  dsimp only
  rw [hF s hk, smul_zero]

theorem gamma_keys_length (s : State) (hs : s ∈ keys (embed localGamma)) :
    s.length = 3 := by
  have h : (keys (embed localGamma)).all (fun s => decide (s.length = 3)) = true := by
    decide
  exact of_decide_eq_true ((List.all_eq_true.mp h) s hs)

variable {Frame Factor : Type*}

/-- A genuine state functional, with its parameter context and remaining
divisor factors explicit. -/
abbrev Functional (Frame Factor M : Type*) := Frame → List Factor → State → M

def gammaValue (t : ℤ) (F : Functional Frame Factor M) (frame : Frame)
    (word : List Factor) : M :=
  realization t (F frame word) (embed localGamma)

theorem gammaValue_nil (t : ℤ) (F : Functional Frame Factor M)
    (hbase : ∀ frame s, s.length = 3 → F frame [] s = 0) (frame : Frame) :
    gammaValue t F frame [] = 0 :=
  realization_zero_of_keys t (F frame []) _ (fun s hs => hbase frame s (gamma_keys_length s hs))

structure Descendant (Frame Factor : Type*) where
  weight : ℤ
  frame : Frame
  word : List Factor

def descendantValue (t : ℤ) (F : Functional Frame Factor M) :
    Option (Descendant Frame Factor) → M
  | none => 0
  | some d => d.weight • gammaValue t F d.frame d.word

/-- Exact equalities needed for one restriction step. `restriction_eq`
is supplied by the genuine native point/diagonal restriction rule;
`rebase_eq` is supplied by actual coordinate pullbacks/permutations.
Neither equality assumes that a modified diagonal vanishes. -/
structure RestrictionStep (t : ℤ) (F : Functional Frame Factor M)
    (frame : Frame) (factor : Factor) (tail : List Factor) where
  kind : LocalKind
  afterRestriction : State → M
  descendant : Option (Descendant Frame Factor)
  length_le : ∀ d, descendant = some d → d.word.length ≤ tail.length
  restriction_eq : gammaValue t F frame (factor :: tail) =
    realization t afterRestriction (action kind)
  rebase_eq : realization t afterRestriction (expected kind) =
    descendantValue t F descendant

/-- Every genuine functional with the stated restriction presentation
annihilates the modified small diagonal against all words of factors.
The proof is induction on factor count, using the checked local rules. -/
theorem gammaValue_zero_of_restrictions (t : ℤ) (F : Functional Frame Factor M)
    (hbase : ∀ frame s, s.length = 3 → F frame [] s = 0)
    (step : ∀ frame factor tail, RestrictionStep t F frame factor tail)
    (frame : Frame) (word : List Factor) : gammaValue t F frame word = 0 := by
  have H : ∀ n : ℕ, ∀ frame word, word.length ≤ n → gammaValue t F frame word = 0 := by
    intro n
    induction n with
    | zero =>
        intro frame word hword
        cases word with
        | nil => exact gammaValue_nil t F hbase frame
        | cons factor tail => simp at hword
    | succ n ih =>
        intro frame word hword
        cases word with
        | nil => exact gammaValue_nil t F hbase frame
        | cons factor tail =>
            let d := step frame factor tail
            have htail : tail.length ≤ n := by simpa using hword
            calc
              gammaValue t F frame (factor :: tail) =
                  realization t d.afterRestriction (action d.kind) := d.restriction_eq
              _ = realization t d.afterRestriction (expected d.kind) :=
                local_realization t d.afterRestriction d.kind
              _ = descendantValue t F d.descendant := d.rebase_eq
              _ = 0 := by
                cases hdesc : d.descendant with
                | none => rfl
                | some e =>
                    change e.weight • gammaValue t F e.frame e.word = 0
                    rw [ih e.frame e.word ((d.length_le e hdesc).trans htail), smul_zero]
  exact H word.length frame word le_rfl

end M9Native.CurvePowerGraphInduction

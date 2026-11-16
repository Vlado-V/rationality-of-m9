module

public import M9StacksIntegration.CurvePowerGraphContextValidity

/-!
# Modified-diagonal induction with computed context descendants

The only geometric input is an exact presentation of the first-factor
restriction by a point or diagonal action in a valid block context.
Every rebase equality and every empty-word vanishing is proved here.
This file does not assert that a native intersection functional has the
required first-factor presentation.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphContextInduction

open CurvePowerGraphLocal CurvePowerGraphInduction CurvePowerGraphContexts
open CurvePowerGraphContextValidity

abbrev ValidContext := {ctx : Context // Valid ctx}

variable {Factor M : Type*} [AddCommGroup M]

def transported (F : List Factor → State → M) : Functional ValidContext Factor M :=
  fun ctx word s => F word (transport ctx.val s)

def child (t : ℤ) (ctx : ValidContext) (kind : LocalKind) : Option (ℤ × ValidContext) :=
  match h : rebase t ctx.val kind with
  | none => none
  | some (w, c) => some (w, ⟨c, valid_rebase t ctx.val ctx.property kind w c h⟩)

theorem child_val (t : ℤ) (ctx : ValidContext) (kind : LocalKind) :
    (child t ctx kind).map (fun (w, c) => (w, c.val)) = rebase t ctx.val kind := by
  unfold child
  split <;> simp_all

def descendant (t : ℤ) (ctx : ValidContext) (kind : LocalKind) (tail : List Factor) :
    Option (Descendant ValidContext Factor) :=
  (child t ctx kind).map fun (w, c) => ⟨w, c, tail⟩

theorem descendant_length (t : ℤ) (ctx : ValidContext) (kind : LocalKind)
    (tail : List Factor) (d : Descendant ValidContext Factor)
    (hd : descendant t ctx kind tail = some d) : d.word.length ≤ tail.length := by
  cases hc : child t ctx kind with
  | none => simp [descendant, hc] at hd
  | some p =>
      rcases p with ⟨w, c⟩
      have he : (⟨w, c, tail⟩ : Descendant ValidContext Factor) = d := by
        simpa only [descendant, hc, Option.map_some, Option.some.injEq] using hd
      rw [← he]

theorem expected_descendant (t : ℤ) (F : List Factor → State → M)
    (ctx : ValidContext) (kind : LocalKind) (tail : List Factor) :
    realization t (F tail ∘ transport ctx.val) (expected kind) =
      descendantValue t (transported F) (descendant t ctx kind tail) := by
  have he := expected_rebase t (F tail) ctx.val kind
  have hv := child_val t ctx kind
  cases hc : child t ctx kind with
  | none =>
      have hr : rebase t ctx.val kind = none := by simpa only [hc, Option.map_none] using hv.symm
      simpa [hr, rebasedValue, descendant, hc, descendantValue] using he
  | some p =>
      rcases p with ⟨w, c⟩
      have hr : rebase t ctx.val kind = some (w, c.val) := by
        simpa only [hc, Option.map_some] using hv.symm
      simp only [descendant, hc, Option.map_some, descendantValue, gammaValue]
      change realization t (F tail ∘ transport ctx.val) (expected kind) =
        w • realization t (F tail ∘ transport c.val) (embed localGamma)
      simpa only [hr, rebasedValue] using he

/-- The actual first restriction may select two spectator blocks as the
active outside labels. Its numerical equality is the exact native
point/diagonal restriction equality, before any vanishing is inferred. -/
structure FirstRestriction (t : ℤ) (F : List Factor → State → M)
    (ctx : ValidContext) (factor : Factor) (tail : List Factor) where
  context : ValidContext
  kind : LocalKind
  restriction_eq : gammaValue t (transported F) ctx (factor :: tail) =
    realization t (F tail ∘ transport context.val) (action kind)

def restrictionStep (t : ℤ) (F : List Factor → State → M)
    (ctx : ValidContext) (factor : Factor) (tail : List Factor)
    (r : FirstRestriction t F ctx factor tail) :
    RestrictionStep t (transported F) ctx factor tail where
  kind := r.kind
  afterRestriction := F tail ∘ transport r.context.val
  descendant := descendant t r.context r.kind tail
  length_le := fun d hd => descendant_length t r.context r.kind tail d hd
  restriction_eq := r.restriction_eq
  rebase_eq := expected_descendant t F r.context r.kind tail

theorem gammaValue_nil (t : ℤ) (F : List Factor → State → M)
    (hbase : ∀ s, 0 < s.length → F [] s = 0) (ctx : ValidContext) :
    gammaValue t (transported F) ctx [] = 0 := by
  apply realization_zero_of_keys
  intro s hs
  exact hbase _ (transport_localGamma_positive ctx.val ctx.property s hs)

/-- Generic induction, with the context rebasing and base case fully
proved. Constructing `FirstRestriction` for the actual native functional
is the remaining geometric step, rather than an assumed vanishing. -/
theorem gammaValue_zero_of_first_restrictions (t : ℤ) (F : List Factor → State → M)
    (hbase : ∀ s, 0 < s.length → F [] s = 0)
    (first : ∀ ctx factor tail, FirstRestriction t F ctx factor tail)
    (ctx : ValidContext) (word : List Factor) :
    gammaValue t (transported F) ctx word = 0 := by
  have H : ∀ n : ℕ, ∀ ctx word, word.length ≤ n →
      gammaValue t (transported F) ctx word = 0 := by
    intro n
    induction n with
    | zero =>
        intro ctx word hw
        cases word with
        | nil => exact gammaValue_nil t F hbase ctx
        | cons factor tail => simp at hw
    | succ n ih =>
        intro ctx word hw
        cases word with
        | nil => exact gammaValue_nil t F hbase ctx
        | cons factor tail =>
            let r := restrictionStep t F ctx factor tail (first ctx factor tail)
            have ht : tail.length ≤ n := by simpa using hw
            calc
              gammaValue t (transported F) ctx (factor :: tail) =
                  realization t r.afterRestriction (action r.kind) := r.restriction_eq
              _ = realization t r.afterRestriction (expected r.kind) :=
                local_realization t r.afterRestriction r.kind
              _ = descendantValue t (transported F) r.descendant := r.rebase_eq
              _ = 0 := by
                cases hd : r.descendant with
                | none => rfl
                | some d =>
                    change d.weight • gammaValue t (transported F) d.frame d.word = 0
                    rw [ih d.frame d.word ((r.length_le d hd).trans ht), smul_zero]
  exact H word.length ctx word le_rfl

end M9Native.CurvePowerGraphContextInduction

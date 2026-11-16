module

public import Mathlib.Tactic

/-!
# Local combinatorics of the modified small diagonal

A state records unmarked diagonal blocks by their bit masks. Every other
vertex is fixed at the chosen point. Coefficients `(a,b)` stand for
`a + b*t`, with `t` the self-diagonal degree. The certificates concern one
point or diagonal restriction of the seven-term modified diagonal on
three distinguished blocks and at most two other blocks.

This is a finite combinatorial certificate. Its realization by the
actual native intersection form and its induction over further factors
are separate geometric obligations.
-/

@[expose] public section

namespace M9Native.CurvePowerGraphLocal

abbrev State := List ℕ
abbrev Coefficient := ℤ × ℤ
abbrev SourceCombination := List (State × ℤ)
abbrev Combination := List (State × Coefficient)

def insertBlock (a : ℕ) : State → State
  | [] => [a]
  | b :: s => if a ≤ b then a :: b :: s else b :: insertBlock a s

def canonical : State → State
  | [] => []
  | a :: s => insertBlock a (canonical s)

def bit (i : ℕ) : ℕ := 2 ^ i

def blockAt (i : ℕ) : State → ℕ
  | [] => 0
  | b :: s => if b.testBit i then b else blockAt i s

def pointStep (i : ℕ) (s : State) : Option State :=
  let b := blockAt i s
  if b = 0 then none else some (s.erase b)

def diagonalStep (i j : ℕ) (s : State) : Option (State × Bool) :=
  let a := blockAt i s
  let b := blockAt j s
  if a = 0 then
    if b = 0 then none else some (s.erase b, false)
  else if b = 0 then some (s.erase a, false)
  else if a = b then some (s.erase a, true)
  else some (canonical ((a ||| b) :: (s.erase a).erase b), false)

def embed (c : SourceCombination) : Combination :=
  c.map fun (s, a) => (s, (a, 0))

def pointAction (i : ℕ) (c : SourceCombination) : Combination :=
  c.flatMap fun (s, a) =>
    match pointStep i s with
    | none => []
    | some s' => [(s', (a, 0))]

def diagonalAction (i j : ℕ) (c : SourceCombination) : Combination :=
  c.flatMap fun (s, a) =>
    match diagonalStep i j s with
    | none => []
    | some (s', loop) => [(s', if loop then (0, a) else (a, 0))]

def gamma (a b c : ℕ) (other : State) : SourceCombination :=
  [(canonical ((a ||| b ||| c) :: other), 1),
   (canonical ((a ||| b) :: other), -1),
   (canonical ((a ||| c) :: other), -1),
   (canonical ((b ||| c) :: other), -1),
   (canonical (c :: other), 1),
   (canonical (b :: other), 1),
   (canonical (a :: other), 1)]

def localGamma : SourceCombination := gamma 1 2 4 [8, 16]

def coefficient (s : State) : Combination → Coefficient
  | [] => 0
  | (u, a) :: c => (if s = u then a else 0) + coefficient s c

def keys (c : Combination) : List State := c.map Prod.fst

def check (c d : Combination) : Bool :=
  (keys c ++ keys d).all fun s => decide (coefficient s c = coefficient s d)

theorem coefficient_zero_of_not_key (c : Combination) (s : State)
    (hs : s ∉ keys c) : coefficient s c = 0 := by
  induction c with
  | nil => rfl
  | cons a c ih =>
      have hne : s ≠ a.1 := by
        intro he
        exact hs (by simp [keys, he])
      have hn : s ∉ keys c := by
        intro h
        exact hs (by simp [keys] at h ⊢; exact Or.inr h)
      simp [coefficient, hne, ih hn]

theorem coefficient_eq_of_check (c d : Combination) (h : check c d = true) (s : State) :
    coefficient s c = coefficient s d := by
  have hh : ∀ s ∈ keys c ++ keys d, coefficient s c = coefficient s d := by
    simpa only [check, List.all_eq_true, decide_eq_true_eq] using h
  by_cases hs : s ∈ keys c ++ keys d
  · exact hh s hs
  · have hc : s ∉ keys c := by simp only [List.mem_append, not_or] at hs; exact hs.1
    have hd : s ∉ keys d := by simp only [List.mem_append, not_or] at hs; exact hs.2
    rw [coefficient_zero_of_not_key c s hc, coefficient_zero_of_not_key d s hd]

def pointExpected (i : ℕ) : Combination :=
  if i < 3 then [] else embed (gamma 1 2 4 ([8, 16].erase (bit i)))

def enlargeSpecial (i j : ℕ) : Combination :=
  embed (gamma
    (if i = 0 then 1 ||| bit j else 1)
    (if i = 1 then 2 ||| bit j else 2)
    (if i = 2 then 4 ||| bit j else 4)
    ([8, 16].erase (bit j)))

def diagonalExpected (i j : ℕ) : Combination :=
  if i = j then (pointExpected i).map fun (s, a) => (s, (0, a.1))
  else if i < 3 then
    if j < 3 then [] else enlargeSpecial i j
  else if j < 3 then enlargeSpecial j i
  else embed (gamma 1 2 4 [bit i ||| bit j])

/-- Pinning any distinguished block kills the modified diagonal;
pinning either other block transports the same relation. -/
theorem point_local_certificate :
    ∀ i : Fin 5, check (pointAction i.val localGamma) (pointExpected i.val) = true := by
  decide

/-- Joining two distinguished blocks kills the modified diagonal;
joining another block transports it. A self-join records the symbolic
self-diagonal factor `t`, so the certificate is independent of genus. -/
theorem diagonal_local_certificate :
    ∀ i j : Fin 5, check (diagonalAction i.val j.val localGamma)
      (diagonalExpected i.val j.val) = true := by
  decide

theorem point_coefficient_eq (i : Fin 5) (s : State) :
    coefficient s (pointAction i.val localGamma) = coefficient s (pointExpected i.val) :=
  coefficient_eq_of_check _ _ (point_local_certificate i) s

theorem diagonal_coefficient_eq (i j : Fin 5) (s : State) :
    coefficient s (diagonalAction i.val j.val localGamma) =
      coefficient s (diagonalExpected i.val j.val) :=
  coefficient_eq_of_check _ _ (diagonal_local_certificate i j) s

/-- The finite certificate as a genuine free additive relation, ready
to be sent to an actual intersection functional. -/
noncomputable def encoded (c : Combination) : State →₀ Coefficient :=
  (c.map fun (s, a) => Finsupp.single s a).sum

theorem encoded_apply (c : Combination) (s : State) : encoded c s = coefficient s c := by
  induction c with
  | nil => simp [encoded, coefficient]
  | cons a c ih =>
      rcases a with ⟨u, a⟩
      simpa [encoded, coefficient, Finsupp.single_apply, eq_comm] using ih

theorem encoded_eq_of_check (c d : Combination) (h : check c d = true) : encoded c = encoded d := by
  apply Finsupp.ext
  intro s
  simpa only [encoded_apply] using coefficient_eq_of_check c d h s

/-- Substitute any integer self-diagonal degree and any actual additive
target. This introduces no geometric premise; it preserves the checked
free relation. -/
noncomputable def realization {M : Type*} [AddCommGroup M]
    (t : ℤ) (F : State → M) (c : Combination) : M :=
  (encoded c).sum fun s a => (a.1 + a.2 * t) • F s

theorem realization_eq_of_check {M : Type*} [AddCommGroup M]
    (t : ℤ) (F : State → M) (c d : Combination) (h : check c d = true) :
    realization t F c = realization t F d := by
  rw [realization, encoded_eq_of_check c d h]
  rfl

theorem point_realization_eq {M : Type*} [AddCommGroup M]
    (t : ℤ) (F : State → M) (i : Fin 5) :
    realization t F (pointAction i.val localGamma) = realization t F (pointExpected i.val) :=
  realization_eq_of_check t F _ _ (point_local_certificate i)

theorem diagonal_realization_eq {M : Type*} [AddCommGroup M]
    (t : ℤ) (F : State → M) (i j : Fin 5) :
    realization t F (diagonalAction i.val j.val localGamma) =
      realization t F (diagonalExpected i.val j.val) :=
  realization_eq_of_check t F _ _ (diagonal_local_certificate i j)

end M9Native.CurvePowerGraphLocal

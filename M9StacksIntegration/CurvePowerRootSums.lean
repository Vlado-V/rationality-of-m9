module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Tactic

/-!
# Power sums for the moving-graph filtration

This is the algebraic induction used after establishing the actual
curve-product intersection relations. It does not assert those geometric
relations or identify a Picard-bundle Chern class.

At each step every old root is shifted by `-p`, and the new root is
`n*p + b`. The three local identities `p^2 = p*b = 0` and
`b^2 = 2*p*firstClass` imply that all root power sums of order at least
two vanish. These are the numerical diagonal relations that must be
proved in the genuine intersection target before applying this file.
-/

@[expose] public section

namespace M9Native.CurvePowerRootSums

variable {R : Type*} [CommRing R]

def powerSum : List R → ℕ → R
  | [], _ => 0
  | a :: r, k => a ^ k + powerSum r k

def nextRoots (n : ℕ) (r : List R) (p b : R) : List R :=
  ((n : R) * p + b) :: r.map (fun a => a - p)

theorem sub_pow_of_sq_zero (a p : R) (hp : p ^ 2 = 0) (n : ℕ) :
    (a - p) ^ (n + 1) = a ^ (n + 1) - (n + 1 : R) * p * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
      calc
        (a - p) ^ (n + 1 + 1) =
            (a ^ (n + 1) - (n + 1 : R) * p * a ^ n) * (a - p) := by
          rw [pow_succ, ih]
        _ = a ^ (n + 1 + 1) - (n + 1 + 1 : R) * p * a ^ (n + 1) +
            (n + 1 : R) * a ^ n * p ^ 2 := by ring
        _ = a ^ (n + 1 + 1) - (n + 1 + 1 : R) * p * a ^ (n + 1) := by
          rw [hp]
          ring

theorem powerSum_zero (r : List R) : powerSum r 0 = (r.length : R) := by
  induction r with
  | nil => simp [powerSum]
  | cons a r ih => simp [powerSum, ih, add_comm]

theorem powerSum_shift (r : List R) (p : R) (hp : p ^ 2 = 0) (k : ℕ) :
    powerSum (r.map (fun a => a - p)) (k + 1) =
      powerSum r (k + 1) - (k + 1 : R) * p * powerSum r k := by
  induction r with
  | nil => simp [powerSum]
  | cons a r ih =>
      simp only [List.map_cons, powerSum, sub_pow_of_sq_zero a p hp k, ih]
      ring

theorem newRoot_sq (n : ℕ) (p b : R) (hp : p ^ 2 = 0) (hpb : p * b = 0) :
    ((n : R) * p + b) ^ 2 = b ^ 2 := by
  calc
    _ = (n : R) ^ 2 * p ^ 2 + 2 * (n : R) * (p * b) + b ^ 2 := by ring
    _ = _ := by rw [hp, hpb]; ring

theorem newRoot_cube (n : ℕ) (p b s : R) (hp : p ^ 2 = 0)
    (hpb : p * b = 0) (hb : b ^ 2 = 2 * p * s) :
    ((n : R) * p + b) ^ 3 = 0 := by
  calc
    _ = (2 * p * s) * ((n : R) * p + b) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, newRoot_sq n p b hp hpb, hb]
    _ = 2 * (n : R) * s * p ^ 2 + 2 * s * (p * b) := by ring
    _ = 0 := by rw [hp, hpb]; ring

theorem newRoot_pow_ge_three (n : ℕ) (p b s : R) (hp : p ^ 2 = 0)
    (hpb : p * b = 0) (hb : b ^ 2 = 2 * p * s) (k : ℕ) :
    ((n : R) * p + b) ^ (k + 3) = 0 := by
  rw [pow_add, newRoot_cube n p b s hp hpb hb, mul_zero]

theorem nextRoots_powerSum_one (n : ℕ) (r : List R) (p b : R) (hp : p ^ 2 = 0) :
    powerSum (nextRoots n r p b) 1 =
      powerSum r 1 - ((r.length : R) - (n : R)) * p + b := by
  change ((n : R) * p + b) ^ 1 + powerSum (r.map (fun a => a - p)) (0 + 1) = _
  rw [powerSum_shift r p hp 0, powerSum_zero]
  simp only [pow_one, Nat.cast_zero, zero_add]
  ring

theorem nextRoots_powerSum_two (n : ℕ) (r : List R) (p b : R)
    (hp : p ^ 2 = 0) (hpb : p * b = 0)
    (hb : b ^ 2 = 2 * p * powerSum r 1) (hs : powerSum r 2 = 0) :
    powerSum (nextRoots n r p b) 2 = 0 := by
  change ((n : R) * p + b) ^ 2 + powerSum (r.map (fun a => a - p)) (1 + 1) = 0
  rw [newRoot_sq n p b hp hpb, hb, powerSum_shift r p hp 1, hs]
  ring

theorem nextRoots_powerSum_ge_three (n : ℕ) (r : List R) (p b s : R)
    (hp : p ^ 2 = 0) (hpb : p * b = 0) (hb : b ^ 2 = 2 * p * s)
    (k : ℕ) (hs : powerSum r (k + 3) = 0) (hprev : powerSum r (k + 2) = 0) :
    powerSum (nextRoots n r p b) (k + 3) = 0 := by
  change ((n : R) * p + b) ^ (k + 3) +
    powerSum (r.map (fun a => a - p)) ((k + 2) + 1) = 0
  rw [newRoot_pow_ge_three n p b s hp hpb hb k, powerSum_shift r p hp (k + 2), hs, hprev]
  ring

def roots (g : ℕ) (p b : ℕ → R) : ℕ → List R
  | 0 => List.replicate g 0
  | n + 1 => nextRoots n (roots g p b n) (p n) (b n)

def firstClass (g : ℕ) (p b : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => firstClass g p b n - (g : R) * p n + b n

theorem roots_length (g : ℕ) (p b : ℕ → R) (n : ℕ) :
    (roots g p b n).length = g + n := by
  induction n with
  | zero => simp [roots]
  | succ n ih => simp [roots, nextRoots, ih]; omega

theorem powerSum_replicate_zero (g k : ℕ) (hk : 0 < k) :
    powerSum (List.replicate g (0 : R)) k = 0 := by
  induction g with
  | zero => simp [powerSum]
  | succ g ih => simp [List.replicate_succ, powerSum, zero_pow hk.ne', ih]

/-- The moving-graph root induction. Its local hypotheses are the
separate geometric diagonal identities, rather than a Chern formula. -/
theorem roots_powerSums (g : ℕ) (p b : ℕ → R)
    (hp : ∀ n, p n ^ 2 = 0) (hpb : ∀ n, p n * b n = 0)
    (hb : ∀ n, b n ^ 2 = 2 * p n * firstClass g p b n) (n : ℕ) :
    powerSum (roots g p b n) 1 = firstClass g p b n ∧
      ∀ k : ℕ, powerSum (roots g p b n) (k + 2) = 0 := by
  induction n with
  | zero =>
      constructor
      · exact powerSum_replicate_zero g 1 (by omega)
      · intro k
        exact powerSum_replicate_zero g (k + 2) (by omega)
  | succ n ih =>
      constructor
      · rw [roots, nextRoots_powerSum_one n _ _ _ (hp n), roots_length, ih.1, firstClass]
        push_cast
        ring
      · intro k
        cases k with
        | zero =>
            apply nextRoots_powerSum_two n _ _ _ (hp n) (hpb n)
            · rw [ih.1]
              exact hb n
            · exact ih.2 0
        | succ k =>
            exact nextRoots_powerSum_ge_three n _ _ _ _ (hp n) (hpb n) (hb n) k
              (ih.2 (k + 1)) (ih.2 k)

end M9Native.CurvePowerRootSums

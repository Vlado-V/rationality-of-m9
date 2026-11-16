module

public import M9StacksIntegration.CurvePowerRootSums
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Chern-series algebra for the genuine moving-graph roots

These are identities for the finite product of the actual linear factors
`1 + a*t`. They apply to the geometric filtration only after its line
classes and their numerical diagonal identities have been proved.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerRootChern

open CurvePowerRootSums

variable {R : Type*} [CommRing R]

def elementary : List R → ℕ → R
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: r, k + 1 => elementary r (k + 1) + a * elementary r k

@[simp] theorem elementary_zero (r : List R) : elementary r 0 = 1 := by
  cases r <;> rfl

def chernSeries : List R → PowerSeries R
  | [] => 1
  | a :: r => (1 + PowerSeries.C a * PowerSeries.X) * chernSeries r

theorem coeff_chernSeries (r : List R) (n : ℕ) :
    PowerSeries.coeff n (chernSeries r) = elementary r n := by
  induction r generalizing n with
  | nil => cases n <;> simp [chernSeries, elementary]
  | cons a r ih =>
      cases n with
      | zero =>
          simp [chernSeries, elementary, PowerSeries.coeff_zero_eq_constantCoeff]
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ih, elementary_zero]
      | succ n =>
          rw [chernSeries, add_mul, one_mul, mul_assoc, map_add,
            PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, ih, ih]
          rfl

theorem elementary_one (r : List R) : elementary r 1 = powerSum r 1 := by
  induction r with
  | nil => rfl
  | cons a r ih => simp [elementary, powerSum, ih, add_comm]

theorem newton_two (r : List R) :
    2 * elementary r 2 = powerSum r 1 ^ 2 - powerSum r 2 := by
  induction r with
  | nil => simp [elementary, powerSum]
  | cons a r ih =>
      simp only [elementary, powerSum, pow_one]
      rw [elementary_one]
      linear_combination ih

theorem newton_three (r : List R) :
    6 * elementary r 3 = powerSum r 1 ^ 3 -
      3 * powerSum r 1 * powerSum r 2 + 2 * powerSum r 3 := by
  induction r with
  | nil => simp [elementary, powerSum]
  | cons a r ih =>
      simp only [elementary, powerSum, pow_one]
      linear_combination ih + 3 * a * newton_two r

theorem newton_four (r : List R) :
    24 * elementary r 4 = powerSum r 1 ^ 4 -
      6 * powerSum r 1 ^ 2 * powerSum r 2 + 3 * powerSum r 2 ^ 2 +
      8 * powerSum r 1 * powerSum r 3 - 6 * powerSum r 4 := by
  induction r with
  | nil => simp [elementary, powerSum]
  | cons a r ih =>
      simp only [elementary, powerSum, pow_one]
      linear_combination ih + 4 * a * newton_three r

theorem newton_five (r : List R) :
    120 * elementary r 5 = powerSum r 1 ^ 5 -
      10 * powerSum r 1 ^ 3 * powerSum r 2 +
      15 * powerSum r 1 * powerSum r 2 ^ 2 +
      20 * powerSum r 1 ^ 2 * powerSum r 3 -
      20 * powerSum r 2 * powerSum r 3 -
      30 * powerSum r 1 * powerSum r 4 + 24 * powerSum r 5 := by
  induction r with
  | nil => simp [elementary, powerSum]
  | cons a r ih =>
      simp only [elementary, powerSum, pow_one]
      linear_combination ih + 5 * a * newton_four r

def elementarySchurMatrix (r : List R) : Matrix (Fin 3) (Fin 3) R :=
  !![elementary r 3, elementary r 4, elementary r 5;
     elementary r 2, elementary r 3, elementary r 4;
     elementary r 1, elementary r 2, elementary r 3]

/-- Clearing the genuine factorial denominators uses only integer
polynomial identities, so no division or reducedness of `R` is needed. -/
theorem elementarySchur_cleared_of_powerSums (r : List R)
    (h2 : powerSum r 2 = 0) (h3 : powerSum r 3 = 0)
    (h4 : powerSum r 4 = 0) (h5 : powerSum r 5 = 0) :
    8640 * (elementarySchurMatrix r).det = powerSum r 1 ^ 9 := by
  have e2 := newton_two r
  have e3 := newton_three r
  have e4 := newton_four r
  have e5 := newton_five r
  simp only [h2, h3, h4, h5, mul_zero, add_zero, sub_zero] at e2 e3 e4 e5
  norm_num [elementarySchurMatrix, Matrix.det_fin_three, elementary_one]
  linear_combination
    (-8640 * elementary r 3 * elementary r 4 +
      2160 * elementary r 5 * (2 * elementary r 2 + powerSum r 1 ^ 2)) * e2 +
    (40 * (36 * elementary r 3 ^ 2 + 6 * elementary r 3 * powerSum r 1 ^ 3 +
      powerSum r 1 ^ 6) - 1440 * powerSum r 1 ^ 2 * elementary r 4 -
      1440 * powerSum r 1 * elementary r 5) * e3 +
    (360 * powerSum r 1 * elementary r 4 - 45 * powerSum r 1 ^ 5) * e4 +
    (6 * powerSum r 1 ^ 4) * e5

def segreSeries (r : List R) : PowerSeries R :=
  PowerSeries.invOfUnit (chernSeries r) 1

def segreCoefficient (r : List R) (n : ℕ) : R :=
  PowerSeries.coeff n (segreSeries r)

@[simp] theorem segreCoefficient_zero (r : List R) : segreCoefficient r 0 = 1 := by
  simp [segreCoefficient, segreSeries, PowerSeries.coeff_invOfUnit]

theorem segreCoefficient_succ (r : List R) (n : ℕ) :
    segreCoefficient r (n + 1) =
      -∑ a ∈ Finset.antidiagonal (n + 1),
        if a.2 < n + 1 then elementary r a.1 * segreCoefficient r a.2 else 0 := by
  rw [segreCoefficient, segreSeries, PowerSeries.coeff_invOfUnit]
  simp only [Nat.succ_ne_zero, ite_false, inv_one, Units.val_one, neg_one_mul,
    coeff_chernSeries, segreCoefficient, segreSeries]

theorem segreCoefficient_one (r : List R) :
    segreCoefficient r 1 = -elementary r 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, segreCoefficient_succ]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]

theorem segreCoefficient_two (r : List R) :
    segreCoefficient r 2 = elementary r 1 ^ 2 - elementary r 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, segreCoefficient_succ]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    segreCoefficient_one]
  ring

theorem segreCoefficient_three (r : List R) :
    segreCoefficient r 3 = -elementary r 1 ^ 3 +
      2 * elementary r 1 * elementary r 2 - elementary r 3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, segreCoefficient_succ]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    segreCoefficient_one, segreCoefficient_two]
  ring

theorem segreCoefficient_four (r : List R) :
    segreCoefficient r 4 = elementary r 1 ^ 4 -
      3 * elementary r 1 ^ 2 * elementary r 2 + elementary r 2 ^ 2 +
      2 * elementary r 1 * elementary r 3 - elementary r 4 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, segreCoefficient_succ]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    segreCoefficient_one, segreCoefficient_two, segreCoefficient_three]
  ring

theorem segreCoefficient_five (r : List R) :
    segreCoefficient r 5 = -elementary r 1 ^ 5 +
      4 * elementary r 1 ^ 3 * elementary r 2 -
      3 * elementary r 1 * elementary r 2 ^ 2 -
      3 * elementary r 1 ^ 2 * elementary r 3 +
      2 * elementary r 2 * elementary r 3 +
      2 * elementary r 1 * elementary r 4 - elementary r 5 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, segreCoefficient_succ]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    segreCoefficient_one, segreCoefficient_two, segreCoefficient_three, segreCoefficient_four]
  ring

def segreSchurMatrix (r : List R) : Matrix (Fin 3) (Fin 3) R :=
  !![segreCoefficient r 3, segreCoefficient r 4, segreCoefficient r 5;
     segreCoefficient r 2, segreCoefficient r 3, segreCoefficient r 4;
     segreCoefficient r 1, segreCoefficient r 2, segreCoefficient r 3]

theorem segreSchur_eq_neg_elementarySchur (r : List R) :
    (segreSchurMatrix r).det = -(elementarySchurMatrix r).det := by
  norm_num [segreSchurMatrix, elementarySchurMatrix, Matrix.det_fin_three,
    segreCoefficient_one, segreCoefficient_two, segreCoefficient_three,
    segreCoefficient_four, segreCoefficient_five]
  ring

/-- The exact integral identity needed by the rank-three obstruction.
Its power-sum hypotheses are provided by the local root-shift induction,
once those local numerical diagonal relations are proved geometrically. -/
theorem segreSchur_cleared_of_powerSums (r : List R)
    (h2 : powerSum r 2 = 0) (h3 : powerSum r 3 = 0)
    (h4 : powerSum r 4 = 0) (h5 : powerSum r 5 = 0) :
    8640 * (segreSchurMatrix r).det = (-powerSum r 1) ^ 9 := by
  rw [segreSchur_eq_neg_elementarySchur, mul_neg,
    elementarySchur_cleared_of_powerSums r h2 h3 h4 h5]
  ring

/-- Combining the local root induction with the finite inverse-series
calculation. The only inputs beyond a commutative ring are the three
local identities supplied by the genuine diagonal geometry. -/
theorem movingRoots_segreSchur_cleared (g : ℕ) (p b : ℕ → R)
    (hp : ∀ n, p n ^ 2 = 0) (hpb : ∀ n, p n * b n = 0)
    (hb : ∀ n, b n ^ 2 = 2 * p n * firstClass g p b n) (n : ℕ) :
    8640 * (segreSchurMatrix (roots g p b n)).det = (-firstClass g p b n) ^ 9 := by
  obtain ⟨h1, hh⟩ := roots_powerSums g p b hp hpb hb n
  simpa only [h1] using segreSchur_cleared_of_powerSums (roots g p b n)
    (hh 0) (hh 1) (hh 2) (hh 3)

end M9Native.CurvePowerRootChern

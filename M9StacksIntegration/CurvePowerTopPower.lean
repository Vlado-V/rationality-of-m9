module

public import M9StacksIntegration.CurvePowerRootChern
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Top powers from the local numerical diagonal relations

This is an integral ring calculation, before geometric realization.
The pair relations must be proved for the genuine curve-product trace
quotient. No theta class, exponential Chern formula, or top-degree
nonvanishing is an input to the calculation.
-/

@[expose] public section

open scoped BigOperators

namespace M9Native.CurvePowerTopPower

open CurvePowerRootSums CurvePowerRootChern

variable {R : Type*} [CommRing R]

def boundary (β : ℕ → ℕ → R) (n : ℕ) : R := ∑ i ∈ Finset.range n, β i n

def pointProduct (p : ℕ → R) (n : ℕ) : R := ∏ i ∈ Finset.range n, p i

theorem pointProduct_succ (p : ℕ → R) (n : ℕ) :
    pointProduct p (n + 1) = pointProduct p n * p n := by
  exact Finset.prod_range_succ p n

theorem pointProduct_mul_eq_zero_of_factor (p : ℕ → R) (n i : ℕ) (hi : i < n)
    (x : R) (hx : p i * x = 0) : pointProduct p n * x = 0 := by
  have hd : p i ∣ pointProduct p n :=
    Finset.dvd_prod_of_mem p (Finset.mem_range.mpr hi)
  obtain ⟨a, ha⟩ := hd
  rw [ha]
  calc
    (p i * a) * x = a * (p i * x) := by ring
    _ = 0 := by rw [hx, mul_zero]

theorem pointProduct_mul_boundary (p : ℕ → R) (β : ℕ → ℕ → R)
    (hleft : ∀ i j, i < j → p i * β i j = 0) (n : ℕ) :
    pointProduct p n * boundary β n = 0 := by
  rw [boundary, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact pointProduct_mul_eq_zero_of_factor p n i (Finset.mem_range.mp hi)
    (β i n) (hleft i n (Finset.mem_range.mp hi))

theorem point_mul_boundary (p : ℕ → R) (β : ℕ → ℕ → R)
    (hright : ∀ i j, i < j → p j * β i j = 0) (n : ℕ) :
    p n * boundary β n = 0 := by
  rw [boundary, Finset.mul_sum]
  exact Finset.sum_eq_zero (fun i hi => hright i n (Finset.mem_range.mp hi))

theorem pointProduct_mul_firstClass (g : ℕ) (p : ℕ → R) (β : ℕ → ℕ → R)
    (hp : ∀ i, p i ^ 2 = 0) (hleft : ∀ i j, i < j → p i * β i j = 0) (n : ℕ) :
    pointProduct p n * firstClass g p (boundary β) n = 0 := by
  induction n with
  | zero => simp only [firstClass, mul_zero]
  | succ n ih =>
      rw [pointProduct_succ, firstClass]
      calc
        (pointProduct p n * p n) *
            (firstClass g p (boundary β) n - (g : R) * p n + boundary β n) =
          p n * (pointProduct p n * firstClass g p (boundary β) n) -
            (g : R) * pointProduct p n * p n ^ 2 +
              p n * (pointProduct p n * boundary β n) := by ring
        _ = 0 := by rw [ih, hp, pointProduct_mul_boundary p β hleft]; ring

theorem boundary_partial_mul_last (p : ℕ → R) (β : ℕ → ℕ → R)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j)
    (m n : ℕ) (hm : m < n) :
    (∑ i ∈ Finset.range m, β i n) * β m n = p n * boundary β m := by
  rw [Finset.sum_mul, boundary, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hcross i m n (Finset.mem_range.mp hi) hm

theorem boundary_partial_sq (g : ℕ) (p : ℕ → R) (β : ℕ → ℕ → R)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -2 * (g : R) * p i * p j)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j)
    (n m : ℕ) (hm : m ≤ n) :
    (∑ i ∈ Finset.range m, β i n) ^ 2 =
      2 * p n * firstClass g p (boundary β) m := by
  induction m with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_pow (by decide : 2 ≠ 0),
      firstClass, mul_zero]
  | succ m ih =>
      have hmn : m < n := by omega
      rw [Finset.sum_range_succ]
      calc
        ((∑ i ∈ Finset.range m, β i n) + β m n) ^ 2 =
            (∑ i ∈ Finset.range m, β i n) ^ 2 +
              2 * ((∑ i ∈ Finset.range m, β i n) * β m n) + β m n ^ 2 := by ring
        _ = 2 * p n * firstClass g p (boundary β) m +
              2 * (p n * boundary β m) + -2 * (g : R) * p m * p n := by
          rw [ih (by omega), boundary_partial_mul_last p β hcross m n hmn, hsquare m n hmn]
        _ = 2 * p n * firstClass g p (boundary β) (m + 1) := by
          rw [firstClass]
          ring

theorem boundary_sq (g : ℕ) (p : ℕ → R) (β : ℕ → ℕ → R)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -2 * (g : R) * p i * p j)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j)
    (n : ℕ) : boundary β n ^ 2 = 2 * p n * firstClass g p (boundary β) n :=
  boundary_partial_sq g p β hsquare hcross n n le_rfl

/-- Truncated binomial expansion supplied solely by the local nilpotent
point and diagonal identities. No inverse of an integer is used. -/
theorem firstClass_step_power (g a p b : R) (hp : p ^ 2 = 0) (hpb : p * b = 0)
    (hb : b ^ 2 = 2 * p * a) (n : ℕ) :
    (a - g * p + b) ^ (n + 1) = a ^ (n + 1) +
      (n + 1 : R) * a ^ n * b + (n + 1 : R) * ((n : R) - g) * p * a ^ n := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
      rw [pow_succ, ih]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      linear_combination
        (a ^ n * ((n : R) + 1)) * hb +
        (a ^ n * ((n : R) + 1) * ((n : R) - 2 * g)) * hpb -
        (a ^ n * ((n : R) + 1) * g * ((n : R) - g)) * hp

def topCoefficient (g : ℕ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => (n + 1 : ℤ) * ((n : ℤ) - g) * topCoefficient g n

theorem firstClass_topPower (g : ℕ) (p : ℕ → R) (β : ℕ → ℕ → R)
    (hp : ∀ i, p i ^ 2 = 0)
    (hleft : ∀ i j, i < j → p i * β i j = 0)
    (hright : ∀ i j, i < j → p j * β i j = 0)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -2 * (g : R) * p i * p j)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j)
    (n : ℕ) :
    firstClass g p (boundary β) n ^ n = (topCoefficient g n : R) * pointProduct p n := by
  induction n with
  | zero => simp [firstClass, topCoefficient, pointProduct]
  | succ n ih =>
      rw [firstClass, firstClass_step_power (g : R) _ _ _ (hp n)
        (point_mul_boundary p β hright n) (boundary_sq g p β hsquare hcross n) n]
      rw [pow_succ, ih]
      have hA := pointProduct_mul_firstClass g p β hp hleft n
      have hB := pointProduct_mul_boundary p β hleft n
      calc
        (topCoefficient g n : R) * pointProduct p n * firstClass g p (boundary β) n +
            (n + 1 : R) * ((topCoefficient g n : R) * pointProduct p n) * boundary β n +
              (n + 1 : R) * ((n : R) - (g : R)) * p n *
                ((topCoefficient g n : R) * pointProduct p n) =
          (topCoefficient g n : R) * (pointProduct p n * firstClass g p (boundary β) n) +
            (n + 1 : R) * (topCoefficient g n : R) * (pointProduct p n * boundary β n) +
              (n + 1 : R) * ((n : R) - (g : R)) * (topCoefficient g n : R) *
                (pointProduct p n * p n) := by ring
        _ = (topCoefficient g (n + 1) : R) * pointProduct p (n + 1) := by
          rw [hA, hB, pointProduct_succ, topCoefficient]
          push_cast
          ring

theorem firstClass_topPower_nine (p : ℕ → R) (β : ℕ → ℕ → R)
    (hp : ∀ i, p i ^ 2 = 0)
    (hleft : ∀ i j, i < j → p i * β i j = 0)
    (hright : ∀ i j, i < j → p j * β i j = 0)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -18 * p i * p j)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j) :
    (-firstClass 9 p (boundary β) 9) ^ 9 = 131681894400 * pointProduct p 9 := by
  have hs : ∀ i j, i < j → β i j ^ 2 = -2 * (9 : R) * p i * p j := by
    intro i j hij
    rw [hsquare i j hij]
    ring
  have ht := firstClass_topPower 9 p β hp hleft hright hs hcross 9
  norm_num [topCoefficient] at ht
  rw [neg_pow, ht]
  norm_num

theorem movingRoots_segreSchur_top_cleared_nine (p : ℕ → R) (β : ℕ → ℕ → R)
    (hp : ∀ i, p i ^ 2 = 0)
    (hleft : ∀ i j, i < j → p i * β i j = 0)
    (hright : ∀ i j, i < j → p j * β i j = 0)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -18 * p i * p j)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j) :
    8640 * (segreSchurMatrix (roots 9 p (boundary β) 9)).det =
      131681894400 * pointProduct p 9 := by
  have hs : ∀ i j, i < j → β i j ^ 2 = -2 * (9 : R) * p i * p j := by
    intro i j hij
    rw [hsquare i j hij]
    ring
  calc
    _ = (-firstClass 9 p (boundary β) 9) ^ 9 :=
      movingRoots_segreSchur_cleared 9 p (boundary β) hp
        (point_mul_boundary p β hright) (boundary_sq 9 p β hs hcross) 9
    _ = _ := firstClass_topPower_nine p β hp hleft hright hsquare hcross

theorem addHom_nat_mul (τ : R →+ ℤ) (n : ℕ) (x : R) :
    τ ((n : R) * x) = (n : ℤ) * τ x := by
  simpa only [nsmul_eq_mul] using map_nsmul τ n x

/-- Once the local pair relations hold in the genuine trace quotient
and the actual product of point fibres has degree one, the integral
Schur trace is fixed. These inputs are explicit geometric obligations. -/
theorem movingRoots_segreSchur_trace_nine (τ : R →+ ℤ) (p : ℕ → R) (β : ℕ → ℕ → R)
    (hp : ∀ i, p i ^ 2 = 0)
    (hleft : ∀ i j, i < j → p i * β i j = 0)
    (hright : ∀ i j, i < j → p j * β i j = 0)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -18 * p i * p j)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j)
    (hpoint : τ (pointProduct p 9) = 1) :
    τ ((segreSchurMatrix (roots 9 p (boundary β) 9)).det) = 15240960 := by
  have h := congrArg τ
    (movingRoots_segreSchur_top_cleared_nine p β hp hleft hright hsquare hcross)
  have hsmall := addHom_nat_mul τ 8640 (segreSchurMatrix (roots 9 p (boundary β) 9)).det
  have hlarge := addHom_nat_mul τ 131681894400 (pointProduct p 9)
  norm_num only [Nat.cast_ofNat] at hsmall hlarge
  rw [hsmall, hlarge, hpoint] at h
  linarith

theorem movingRoots_segreSchur_ne_zero_nine (τ : R →+ ℤ) (p : ℕ → R) (β : ℕ → ℕ → R)
    (hp : ∀ i, p i ^ 2 = 0)
    (hleft : ∀ i j, i < j → p i * β i j = 0)
    (hright : ∀ i j, i < j → p j * β i j = 0)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -18 * p i * p j)
    (hcross : ∀ i j n, i < j → j < n → β i n * β j n = p n * β i j)
    (hpoint : τ (pointProduct p 9) = 1) :
    (segreSchurMatrix (roots 9 p (boundary β) 9)).det ≠ 0 := by
  intro he
  have h := movingRoots_segreSchur_trace_nine τ p β hp hleft hright hsquare hcross hpoint
  rw [he, map_zero] at h
  norm_num at h

end M9Native.CurvePowerTopPower

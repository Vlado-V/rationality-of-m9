module

public import M9StacksIntegration.LagrangianDegreeArithmetic
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Exact ordered flag-normalizer arithmetic

These are integer polynomial identities, not geometric pushforward
claims. They retain the actual quotient-flag normalizer x1²x2 and the
ordered Vandermonde sign needed by the later genuine Gysin steps.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace M9Native.LagrangianDegree

/-- Reversing the three quotient roots changes the Vandermonde sign. -/
theorem degreePolynomial_reverse :
    rename (Equiv.swap (0 : Fin 3) 2) degreePolynomial = -degreePolynomial := by
  simp only [degreePolynomial, map_mul, map_add, map_sub, map_pow, rename_X]
  norm_num [Equiv.swap_apply_def]
  set a := (X 0 : MvPolynomial (Fin 3) ℤ)
  set b := (X 1 : MvPolynomial (Fin 3) ℤ)
  set c := (X 2 : MvPolynomial (Fin 3) ℤ)
  have hsum : c + b + a = a + b + c := by ac_rfl
  rw [hsum, add_comm c b, add_comm c a, add_comm b a,
    ← neg_sub b c, ← neg_sub a c, ← neg_sub a b]
  simp only [mul_neg, neg_mul, neg_neg]
  congr 1
  ac_rfl

/-- The reverse ordered exponent, for the same literal polynomial. -/
def reverseDegreeExponent : Fin 3 →₀ ℕ :=
  Finsupp.single 0 3 + Finsupp.single 1 4 + Finsupp.single 2 5

theorem degreePolynomial_reverse_coefficient :
    degreePolynomial.coeff reverseDegreeExponent = -16 := by
  have hd : degreeExponent.mapDomain (Equiv.swap (0 : Fin 3) 2) =
      reverseDegreeExponent := by
    simp [degreeExponent, reverseDegreeExponent, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, Equiv.swap_apply_def]
    abel
  have h := coeff_rename_mapDomain (Equiv.swap (0 : Fin 3) 2)
    (Equiv.swap (0 : Fin 3) 2).injective degreePolynomial degreeExponent
  rw [hd, degreePolynomial_reverse, MvPolynomial.coeff_neg,
    degreePolynomial_coefficient] at h
  linarith

/-- The normalizing class on the original rank-three quotient flag. -/
def flagNormalizer : MvPolynomial (Fin 3) ℤ := X 0^2 * X 1

/-- The top exponent for the six-dimensional trivial ambient bundle. -/
def flagTopExponent : Fin 3 →₀ ℕ :=
  Finsupp.single 0 5 + Finsupp.single 1 5 + Finsupp.single 2 5

theorem flagNormalizer_eq_monomial :
    flagNormalizer = monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 := by
  simp [flagNormalizer, MvPolynomial.X, MvPolynomial.monomial_pow,
    MvPolynomial.monomial_mul_monomial]

/-- This coefficient is negative sixteen. The later geometric Gysin
comparison must derive the compensating ordered Vandermonde minus sign. -/
theorem flag_normalized_coefficient :
    (flagNormalizer * degreePolynomial).coeff flagTopExponent = -16 := by
  have hd : flagTopExponent =
      (Finsupp.single 0 2 + Finsupp.single 1 1) + reverseDegreeExponent := by
    ext i
    fin_cases i <;> norm_num [flagTopExponent, reverseDegreeExponent]
  rw [flagNormalizer_eq_monomial, hd, MvPolynomial.coeff_monomial_mul,
    one_mul, degreePolynomial_reverse_coefficient]

end M9Native.LagrangianDegree

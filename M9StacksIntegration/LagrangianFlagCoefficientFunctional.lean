module

public import M9StacksIntegration.LagrangianFlagArithmetic

/-!
# The coefficient functional of the actual positive quotient-root order

This arithmetic leaf records the sign of the six coefficients that the
geometric free-six flag pushes must produce. It does not assert a
geometric pushforward formula.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace M9Native.LagrangianFlagCoefficientFunctional

abbrev exponent (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

/-- The literal integrand on the normalized quotient flag. -/
def integrand : MvPolynomial (Fin 3) ℤ :=
  X 0^2 * X 1 * (X 0+X 1) * (X 0+X 2) * (X 1+X 2) * (X 0+X 1+X 2)^6

/-- The six-term functional in the actual successive fibre order5,4,3. -/
def functional (p : MvPolynomial (Fin 3) ℤ) : ℤ :=
  p.coeff (exponent 5 4 3) - p.coeff (exponent 4 5 3) - p.coeff (exponent 5 3 4) +
    p.coeff (exponent 3 5 4) + p.coeff (exponent 4 3 5) - p.coeff (exponent 3 4 5)

private theorem monomial_exponent (a b c : ℕ) :
    monomial (exponent a b c) (1:ℤ) = X 0^a * X 1^b * X 2^c := by
  simp [exponent, MvPolynomial.X, monomial_pow, monomial_mul_monomial]

/-- Each top-coefficient shift is an ordinary finite monomial shift. -/
theorem coefficient_shift (p : MvPolynomial (Fin 3) ℤ) (a b c : ℕ)
    (ha : a≤5) (hb : b≤5) (hc : c≤5) :
    (p * monomial (exponent a b c) 1).coeff LagrangianDegree.flagTopExponent =
      p.coeff (exponent (5-a) (5-b) (5-c)) := by
  have h : LagrangianDegree.flagTopExponent =
      exponent (5-a) (5-b) (5-c) + exponent a b c := by
    ext i
    fin_cases i <;> simp [LagrangianDegree.flagTopExponent,exponent] <;> omega
  rw [h,coeff_mul_monomial,mul_one]

/-- The compensating negative Vandermonde sign is proved for every polynomial. -/
theorem functional_eq_neg_vandermonde_coefficient (p : MvPolynomial (Fin 3) ℤ) :
    functional p =
      -(p * ((X 0-X 1)*(X 0-X 2)*(X 1-X 2))).coeff LagrangianDegree.flagTopExponent := by
  have hv : ((X 0-X 1)*(X 0-X 2)*(X 1-X 2) : MvPolynomial (Fin 3) ℤ) =
      monomial (exponent 2 1 0) 1 - monomial (exponent 2 0 1) 1 -
      monomial (exponent 1 2 0) 1 + monomial (exponent 1 0 2) 1 +
      monomial (exponent 0 2 1) 1 - monomial (exponent 0 1 2) 1 := by
    simp only [monomial_exponent]
    ring
  rw [hv]
  simp only [mul_sub,mul_add,coeff_sub,AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  rw [coefficient_shift p 2 1 0 (by omega) (by omega) (by omega),
    coefficient_shift p 2 0 1 (by omega) (by omega) (by omega),
    coefficient_shift p 1 2 0 (by omega) (by omega) (by omega),
    coefficient_shift p 1 0 2 (by omega) (by omega) (by omega),
    coefficient_shift p 0 2 1 (by omega) (by omega) (by omega),
    coefficient_shift p 0 1 2 (by omega) (by omega) (by omega)]
  norm_num only [Nat.reduceSub]
  unfold functional
  abel

/-- Apply the frozen normalized coefficient, with its actual proved sign. -/
theorem functional_integrand : functional integrand = 16 := by
  rw [functional_eq_neg_vandermonde_coefficient]
  have h : integrand * ((X 0-X 1)*(X 0-X 2)*(X 1-X 2)) =
      LagrangianDegree.flagNormalizer * LagrangianDegree.degreePolynomial := by
    unfold integrand LagrangianDegree.flagNormalizer LagrangianDegree.degreePolynomial
    simp only [mul_assoc]
  rw [h,LagrangianDegree.flag_normalized_coefficient]
  norm_num

end M9Native.LagrangianFlagCoefficientFunctional

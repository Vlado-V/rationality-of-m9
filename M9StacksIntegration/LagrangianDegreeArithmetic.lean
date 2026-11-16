module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Tactic

/-! The exact final integer coefficient in the quotient-root LG flag
calculation. This is an arithmetic identity only: the geometric
zero-locus and Gysin comparisons are separate required theorems. -/

@[expose] public noncomputable section

namespace M9Native.LagrangianDegree

open MvPolynomial

private theorem coeff_add_point (p q : MvPolynomial (Fin 3) ℤ) (d : Fin 3 →₀ ℕ) :
    (p + q).coeff d = p.coeff d + q.coeff d :=
  DFunLike.congr_fun (AddMonoidAlgebra.coeff_add p q) d

private theorem coeff_mul_nat (p : MvPolynomial (Fin 3) ℤ) (n : ℕ)
    (d : Fin 3 →₀ ℕ) : (p * (n : MvPolynomial (Fin 3) ℤ)).coeff d =
      p.coeff d * (n : ℤ) := by
  rw [← MvPolynomial.C_eq_coe_nat n, mul_comm, MvPolynomial.coeff_C_mul, mul_comm]

private theorem coeff_mul_ofNat (p : MvPolynomial (Fin 3) ℤ) (n : ℕ) [n.AtLeastTwo]
    (d : Fin 3 →₀ ℕ) : (p * (ofNat(n) : MvPolynomial (Fin 3) ℤ)).coeff d =
      p.coeff d * (ofNat(n) : ℤ) := by
  simpa only [Nat.cast_ofNat] using coeff_mul_nat p (ofNat(n)) d

/-- Exponents in the ordered quotient-root convention. -/
def degreeExponent : Fin 3 →₀ ℕ :=
  Finsupp.single 0 5 + Finsupp.single 1 4 + Finsupp.single 2 3

/-- The rank-three exterior-square top class, six hyperplane factors,
and the ordered quotient-root Vandermonde. -/
def degreePolynomial : MvPolynomial (Fin 3) ℤ :=
  (X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2) *
    (X 0 + X 1 + X 2)^6 * (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)

theorem degreePolynomial_coefficient :
    degreePolynomial.coeff degreeExponent = 16 := by
  unfold degreePolynomial degreeExponent
  conv_lhs => arg 1; ring_nf
  simp only [coeff_add_point, MvPolynomial.coeff_sub]
  norm_num [coeff_mul_ofNat, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X,
    MvPolynomial.monomial_pow, ← MvPolynomial.C_eq_coe_nat, MvPolynomial.C,
    MvPolynomial.monomial_mul_monomial, coeff_add_point,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ]

/-- The same ordered Vandermonde sends the normalized point class to1;
this fixes the quotient-root orientation and sign. -/
theorem pointClass_coefficient :
    (((X 0 * X 1 * X 2 : MvPolynomial (Fin 3) ℤ)^3) *
      (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)).coeff degreeExponent = 1 := by
  unfold degreeExponent
  conv_lhs => arg 1; ring_nf
  simp only [coeff_add_point, MvPolynomial.coeff_sub]
  norm_num [coeff_mul_ofNat, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X,
    MvPolynomial.monomial_pow, ← MvPolynomial.C_eq_coe_nat, MvPolynomial.C,
    MvPolynomial.monomial_mul_monomial, coeff_add_point,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ]

end M9Native.LagrangianDegree

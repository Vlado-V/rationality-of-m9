module

public import M9StacksIntegration.CurvePowerPointTrace
public import M9StacksIntegration.CurvePowerDiagonalAlgebra

/-! Pure word-law consequences for the genuine polynomial trace radical.
The only hypotheses concern permutation invariance and the displayed
literal prefixes against every word tail. No polynomial-test vanishing
or geometric trace realization is assumed. -/

@[expose] public noncomputable section
set_option maxRecDepth 4096

namespace M9Native.PolynomialTraceRelations

open MvPolynomial CurvePowerTraceRadical CurvePowerPolynomialTrace CurvePowerPointTrace

variable {α : Type*} (F : List α → ℤ)
    (hF : ∀ u v : List α, u.Perm v → F u = F v)

abbrev radical : Ideal (MvPolynomial α ℤ) := traceRadical (trace F)

include hF

/-- Multiplying a prefix polynomial by a monomial is precisely appending
its factor word, by the proved permutation invariance. -/
theorem trace_prefix_monomial (headWord : List α) (e : α →₀ ℕ) :
    trace F (wordPolynomial headWord * monomial e 1) = F (headWord ++ word e) := by
  rw [wordPolynomial_eq_monomial, trace_monomial_mul_monomial F hF, one_mul, one_smul]
  exact hF _ _ ((canonicalWord_perm headWord).append (List.Perm.refl _))

theorem trace_pair_monomial (p q : α) (e : α →₀ ℕ) :
    trace F ((X p * X q) * monomial e 1) = F (p :: q :: word e) := by
  simpa only [wordPolynomial, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, List.cons_append, List.nil_append] using
      trace_prefix_monomial F hF [p,q] e

theorem trace_single_monomial (p : α) (e : α →₀ ℕ) :
    trace F (X p * monomial e 1) = F (p :: word e) := by
  simpa only [one_smul] using trace_X_mul_monomial F hF p e 1

omit hF in
/-- Integer polynomial coefficients act by the literal integer scalar on trace values. -/
theorem trace_coefficient_monomial (t : ℤ) (r : MvPolynomial α ℤ) (e : α →₀ ℕ) :
    trace F ((C t * r) * monomial e 1) = t * trace F (r * monomial e 1) := by
  rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul, map_zsmul, zsmul_eq_mul]
  simp only [Int.cast_id]

/-- A literal repeated-point word law annihilates the square against all
polynomials, through the proved monomial-pairing criterion. -/
theorem square_mem_radical (p : α)
    (hp : ∀ tail : List α, F (p :: p :: tail) = 0) :
    (X p : MvPolynomial α ℤ) ^ 2 ∈ radical F := by
  apply mem_radical_of_monomial_pairings
  intro e
  rw [pow_two, trace_pair_monomial F hF]
  exact hp (word e)

theorem pair_difference_mem_radical (a b c d : α)
    (hab : ∀ tail : List α, F (a :: b :: tail) = F (c :: d :: tail)) :
    (X a * X b - X c * X d : MvPolynomial α ℤ) ∈ radical F := by
  apply mem_radical_of_monomial_pairings
  intro e
  rw [sub_mul, map_sub, trace_pair_monomial F hF, trace_pair_monomial F hF,
    hab (word e), sub_self]

theorem incidence_mem_radical (p q d : α)
    (hpd : ∀ tail : List α, F (p :: d :: tail) = F (p :: q :: tail)) :
    (X p * X d - X p * X q : MvPolynomial α ℤ) ∈ radical F := by
  apply mem_radical_of_monomial_pairings
  intro e
  rw [sub_mul, map_sub, trace_pair_monomial F hF, trace_pair_monomial F hF,
    hpd (word e), sub_self]

theorem diagonal_square_mem_radical (t : ℤ) (p q d : α)
    (hd : ∀ tail : List α, F (d :: d :: tail) = t * F (p :: q :: tail)) :
    ((X d)^2 - C t * X p * X q : MvPolynomial α ℤ) ∈ radical F := by
  apply mem_radical_of_monomial_pairings
  intro e
  rw [sub_mul, map_sub, pow_two, trace_pair_monomial F hF]
  have hm : C t * X p * X q = C t * (X p * X q : MvPolynomial α ℤ) := mul_assoc _ _ _
  rw [hm, trace_coefficient_monomial, trace_pair_monomial F hF, hd (word e), sub_self]

theorem self_mem_radical (t : ℤ) (s p : α)
    (hs : ∀ tail : List α, F (s :: tail) = t * F (p :: tail)) :
    (X s - C t * X p : MvPolynomial α ℤ) ∈ radical F := by
  apply mem_radical_of_monomial_pairings
  intro e
  rw [sub_mul, map_sub, trace_single_monomial F hF,
    trace_coefficient_monomial, trace_single_monomial F hF, hs (word e), sub_self]

/-- The seven literal two-letter prefixes give the genuine modified
triple polynomial relation in the trace radical. -/
theorem modifiedTriple_mem_radical (p q r d e f : α)
    (htriple : ∀ tail : List α,
      F (e :: f :: tail) - F (e :: q :: tail) - F (f :: p :: tail) - F (d :: r :: tail) +
        F (p :: q :: tail) + F (p :: r :: tail) + F (q :: r :: tail) = 0) :
    CurvePowerDiagonalAlgebra.modifiedTriple (X p) (X q) (X r) (X d) (X e) (X f) ∈ radical F := by
  apply mem_radical_of_monomial_pairings
  intro a
  simp only [CurvePowerDiagonalAlgebra.modifiedTriple, add_mul, sub_mul, map_add, map_sub,
    trace_pair_monomial F hF]
  exact htriple (word a)

omit hF

/-- The actual quotient by all product pairings of the constructed trace. -/
abbrev TraceQuotient := MvPolynomial α ℤ ⧸ radical F

/-- A divisor label in the actual trace quotient. -/
def pointClass (i : α) : TraceQuotient F := Ideal.Quotient.mk (radical F) (X i)

theorem quotient_C (t : ℤ) :
    Ideal.Quotient.mk (radical F) (C t) = (t : TraceQuotient F) := by
  have h := map_intCast (Ideal.Quotient.mk (radical F)) t
  simpa only [← map_intCast (C : ℤ →+* MvPolynomial α ℤ), Int.cast_id] using h

include hF

theorem pointClass_square (p : α)
    (hp : ∀ tail : List α, F (p :: p :: tail) = 0) :
    pointClass F p ^ 2 = 0 := by
  change Ideal.Quotient.mk (radical F) (X p) ^ 2 = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact square_mem_radical F hF p hp

theorem pointClass_pair_eq (a b c d : α)
    (hab : ∀ tail : List α, F (a :: b :: tail) = F (c :: d :: tail)) :
    pointClass F a * pointClass F b = pointClass F c * pointClass F d := by
  have h := Ideal.Quotient.eq.mpr (pair_difference_mem_radical F hF a b c d hab)
  simpa only [pointClass, map_mul] using h

theorem pointClass_diagonal_square (t : ℤ) (p q d : α)
    (hd : ∀ tail : List α, F (d :: d :: tail) = t * F (p :: q :: tail)) :
    pointClass F d ^ 2 = (t : TraceQuotient F) * pointClass F p * pointClass F q := by
  have h := Ideal.Quotient.eq.mpr (diagonal_square_mem_radical F hF t p q d hd)
  simpa only [pointClass, map_pow, map_mul, quotient_C] using h

theorem pointClass_self (t : ℤ) (s p : α)
    (hs : ∀ tail : List α, F (s :: tail) = t * F (p :: tail)) :
    pointClass F s = (t : TraceQuotient F) * pointClass F p := by
  have h := Ideal.Quotient.eq.mpr (self_mem_radical F hF t s p hs)
  simpa only [pointClass, map_mul, quotient_C] using h

theorem pointClass_modifiedTriple (p q r d e f : α)
    (htriple : ∀ tail : List α,
      F (e :: f :: tail) - F (e :: q :: tail) - F (f :: p :: tail) - F (d :: r :: tail) +
        F (p :: q :: tail) + F (p :: r :: tail) + F (q :: r :: tail) = 0) :
    CurvePowerDiagonalAlgebra.modifiedTriple
      (pointClass F p) (pointClass F q) (pointClass F r)
      (pointClass F d) (pointClass F e) (pointClass F f) = 0 := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (modifiedTriple_mem_radical F hF p q r d e f htriple)
  simpa only [CurvePowerDiagonalAlgebra.modifiedTriple, pointClass,
    map_add, map_sub, map_mul] using h

/-- The reduced diagonal square is forced by the literal word laws;
no relation in the quotient is assumed separately. -/
theorem reducedDiagonal_sq (t : ℤ) (p q d : α)
    (hp : ∀ tail : List α, F (p :: p :: tail) = 0)
    (hq : ∀ tail : List α, F (q :: q :: tail) = 0)
    (hpd : ∀ tail : List α, F (p :: d :: tail) = F (p :: q :: tail))
    (hqd : ∀ tail : List α, F (q :: d :: tail) = F (p :: q :: tail))
    (hd : ∀ tail : List α, F (d :: d :: tail) = t * F (p :: q :: tail)) :
    CurvePowerDiagonalAlgebra.reducedDiagonal
        (pointClass F p) (pointClass F q) (pointClass F d) ^ 2 =
      ((t : TraceQuotient F) - 2) * pointClass F p * pointClass F q := by
  exact CurvePowerDiagonalAlgebra.reducedDiagonal_sq _ _ _ _
    (pointClass_square F hF p hp) (pointClass_square F hF q hq)
    (pointClass_pair_eq F hF p d p q hpd) (pointClass_pair_eq F hF q d p q hqd)
    (pointClass_diagonal_square F hF t p q d hd)

/-- The reduced cross relation is likewise derived from all-tail word laws. -/
theorem reducedDiagonal_cross (p q r d e f : α)
    (hr : ∀ tail : List α, F (r :: r :: tail) = 0)
    (hre : ∀ tail : List α, F (r :: e :: tail) = F (p :: r :: tail))
    (hrf : ∀ tail : List α, F (r :: f :: tail) = F (q :: r :: tail))
    (htriple : ∀ tail : List α,
      F (e :: f :: tail) - F (e :: q :: tail) - F (f :: p :: tail) - F (d :: r :: tail) +
        F (p :: q :: tail) + F (p :: r :: tail) + F (q :: r :: tail) = 0) :
    CurvePowerDiagonalAlgebra.reducedDiagonal (pointClass F p) (pointClass F r) (pointClass F e) *
      CurvePowerDiagonalAlgebra.reducedDiagonal (pointClass F q) (pointClass F r) (pointClass F f) =
      pointClass F r * CurvePowerDiagonalAlgebra.reducedDiagonal
        (pointClass F p) (pointClass F q) (pointClass F d) := by
  exact CurvePowerDiagonalAlgebra.reducedDiagonal_cross _ _ _ _ _ _
    (pointClass_square F hF r hr)
    (pointClass_pair_eq F hF r e p r hre) (pointClass_pair_eq F hF r f q r hrf)
    (pointClass_modifiedTriple F hF p q r d e f htriple)

end M9Native.PolynomialTraceRelations

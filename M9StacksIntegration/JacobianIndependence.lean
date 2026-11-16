module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

/-!
# An algebraic Jacobian criterion for rational coordinates

In characteristic zero an invertible matrix of actual derivation values
implies algebraic independence. The proof differentiates a relation of
minimal total degree; no dominance or independence is assumed.
-/

@[expose] public noncomputable section

namespace M9Native.JacobianIndependence

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι]

omit [CharZero K] in
theorem pderiv_totalDegree_lt (p : MvPolynomial ι K) (i : ι)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hcoeff (m : ι →₀ ℕ) (hm : m ∈ (pderiv i p).support) :
      m.sum (fun _ e => e) + 1 ≤ p.totalDegree := by
    have hc : (pderiv i p).coeff m ≠ 0 := mem_support_iff.mp hm
    rw [coeff_pderiv] at hc
    have hp : m + Finsupp.single i 1 ∈ p.support :=
      mem_support_iff.mpr (left_ne_zero_of_mul hc)
    have hd := le_totalDegree hp
    simpa [Finsupp.sum_fintype,Finset.sum_add_distrib] using hd
  have hpos : 0 < p.totalDegree := by
    obtain ⟨m,hm⟩ := support_nonempty.mpr h
    have := hcoeff m hm
    omega
  rw [totalDegree,Finset.sup_lt_iff hpos]
  intro m hm
  have := hcoeff m hm
  omega

omit [Fintype ι] in
/-- Vanishing of all partial derivatives forces a literal constant polynomial. -/
theorem eq_C_of_pderiv_eq_zero (p : MvPolynomial ι K) (h : ∀ i, pderiv i p = 0) :
    p = C (p.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · simp [hm]
  rw [coeff_C,ite_eq_right (Ne.symm hm)]
  obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hm
  have hle : Finsupp.single i 1 ≤ m :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hexp : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
    tsub_add_cancel_of_le hle
  let m' : ι →₀ ℕ := m - Finsupp.single i 1
  have hc := congrArg (fun f : MvPolynomial ι K => f.coeff (m - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv,hexp] at hc
  change p.coeff m * ((m' i : K) + 1) = 0 at hc
  exact (mul_eq_zero.mp hc).resolve_right (by exact_mod_cast Nat.succ_ne_zero (m' i))

variable {L : Type*} [Field L] [Algebra K L]

omit [CharZero K] in
/-- The finite chain rule, for an arbitrary actual derivation on the target algebra. -/
theorem derivation_aeval (D : Derivation K L L) (x : ι → L) (p : MvPolynomial ι K) :
    D (aeval x p) = ∑ j, aeval x (pderiv j p) * D (x j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq,add_mul,Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul,aeval_X,Derivation.leibniz,hp,smul_eq_mul,
      map_add,pderiv_X,Pi.single_apply,apply_ite,map_zero,mul_one,mul_zero]
    simp only [add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ac_rfl

/-- A nonsingular actual Jacobian rules out every nonzero polynomial relation. -/
theorem algebraicIndependent_of_derivations [DecidableEq ι]
    (D : ι → Derivation K L L) (x : ι → L)
    (hJ : (Matrix.of (fun i j => D i (x j))).det ≠ 0) :
    AlgebraicIndependent K x := by
  classical
  rw [algebraicIndependent_iff]
  have hmain : ∀ n, ∀ p : MvPolynomial ι K, p.totalDegree = n → aeval x p = 0 → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdeg hp
      let c : ι → L := fun j => aeval x (pderiv j p)
      have hJc : (Matrix.of (fun i j => D i (x j))).mulVec c = 0 := by
        funext i
        have hh := derivation_aeval (D i) x p
        rw [hp,map_zero] at hh
        simpa only [Matrix.mulVec,dotProduct,Matrix.of_apply,c,mul_comm,Pi.zero_apply] using hh.symm
      have hc : c = 0 := by
        apply (Matrix.mulVec_injective_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hJ)))
        simpa only [Matrix.mulVec_zero] using hJc
      have hpd : ∀ i, pderiv i p = 0 := by
        intro i
        by_contra hi
        have hd := pderiv_totalDegree_lt p i hi
        rw [hdeg] at hd
        exact hi (ih _ hd _ rfl (congrFun hc i))
      have hconst := eq_C_of_pderiv_eq_zero p hpd
      rw [hconst,aeval_C] at hp
      have hcoeff : p.coeff 0 = 0 := (algebraMap K L).injective (by simpa using hp)
      rw [hconst,hcoeff,C_0]
  intro p hp
  exact hmain p.totalDegree p rfl hp

end M9Native.JacobianIndependence

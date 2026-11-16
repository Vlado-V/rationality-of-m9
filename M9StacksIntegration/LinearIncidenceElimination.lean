module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Tactic

/-! Exact elimination of the universal linear-incidence equations on a chart
where one nonpivot coefficient is a unit. Five equations eliminate five
independent matrix entries, leaving forty actual polynomial coordinates. -/

@[expose] public noncomputable section

open scoped BigOperators
open MvPolynomial

universe u v w

namespace M9Native.LinearIncidenceElimination

variable {R : Type u} [CommRing R] {α : Type v} {β : Type w} [Fintype β]

abbrev Full := MvPolynomial (α × Option β) R
abbrev Rest := MvPolynomial (α × β) R

variable (b : α → R) (a : β → R) (u : Rˣ)

def remainder (i : α) : Rest (R:=R) (α:=α) (β:=β) :=
  C (b i) + ∑ j : β,C (a j)*X (i,j)

def equation (i : α) : Full (R:=R) (α:=α) (β:=β) :=
  C (b i) + C (u : R)*X (i,none) + ∑ j : β,C (a j)*X (i,some j)

def ideal : Ideal (Full (R:=R) (α:=α) (β:=β)) := Ideal.span (Set.range (equation b a u))

abbrev Ring := Full (R:=R) (α:=α) (β:=β) ⧸ ideal b a u

def substitute (v : α × Option β) : Rest (R:=R) (α:=α) (β:=β) :=
  match v.2 with
  | none => -C (↑u⁻¹ : R)*remainder b a v.1
  | some j => X (v.1,j)

def evaluate : Full (R:=R) (α:=α) (β:=β) →ₐ[R] Rest (R:=R) (α:=α) (β:=β) :=
  aeval (substitute b a u)

theorem evaluate_equation (i : α) : evaluate b a u (equation b a u i)=0 := by
  simp only [evaluate,equation,map_add,map_sum,map_mul,aeval_C,aeval_X,substitute,
    algebraMap_eq]
  have hunit : (C (u : R) : Rest (R:=R) (α:=α) (β:=β))*C (↑u⁻¹ : R)=1 := by
    rw [← C_mul,Units.mul_inv, C_1]
  rw [neg_mul,mul_neg,← mul_assoc,hunit,one_mul,remainder]
  ring

theorem ideal_le_ker : ideal b a u ≤ RingHom.ker (evaluate b a u).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact evaluate_equation b a u i

def forward : Ring b a u →ₐ[R] Rest (R:=R) (α:=α) (β:=β) :=
  Ideal.Quotient.liftₐ _ (evaluate b a u) (fun _ h => ideal_le_ker b a u h)

@[simp] theorem forward_mk (p : Full (R:=R) (α:=α) (β:=β)) :
    forward b a u (Ideal.Quotient.mk (ideal b a u) p)=evaluate b a u p := rfl

def backward : Rest (R:=R) (α:=α) (β:=β) →ₐ[R] Ring b a u :=
  aeval (fun v => Ideal.Quotient.mk (ideal b a u) (X (v.1,some v.2)))

theorem forward_backward : (forward b a u).comp (backward b a u)=AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [backward,evaluate,substitute]

theorem backward_forward : (backward b a u).comp (forward b a u)=AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with ⟨i,j⟩
  cases j with
  | some j => simp [backward,evaluate,substitute]
  | none =>
    let q := Ideal.Quotient.mkₐ R (ideal b a u)
    have hz : q (equation b a u i)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    have hunit : (algebraMap R (Ring b a u) (↑u⁻¹ : R))*algebraMap R (Ring b a u) (u : R)=1 := by
      rw [← map_mul,Units.inv_mul,map_one]
    change backward b a u (evaluate b a u (X (i,none)))=q (X (i,none))
    simp only [evaluate,aeval_X,substitute,map_mul,map_neg,remainder,map_add,map_sum,
      backward,aeval_C,aeval_X]
    have hqC (r : R) : q (C r)=algebraMap R (Ring b a u) r := q.commutes r
    simp only [equation,map_add,map_mul,map_sum,hqC] at hz
    have h := congrArg (fun z : Ring b a u => algebraMap R (Ring b a u) (↑u⁻¹ : R)*z) hz
    simp only [mul_add,← mul_assoc,hunit,one_mul,mul_zero] at h
    simp only [q,Ideal.Quotient.mkₐ_eq_mk] at h ⊢
    linear_combination -h

def quotientEquiv : Ring b a u ≃ₐ[R] Rest (R:=R) (α:=α) (β:=β) :=
  AlgEquiv.ofAlgHom (forward b a u) (backward b a u)
    (forward_backward b a u) (backward_forward b a u)

/-- On the actual normalized incidence equations, all coefficients are generated
by the nonpivot coefficients. Thus their basic opens cover the incidence chart. -/
theorem nonpivot_span_eq_top (b : α → R) (a : β → R) (A : α → β → R)
    (hzero : ∀ i,b i + ∑ j : β,A i j*a j=0)
    (hfull : Ideal.span (Set.range b ∪ Set.range a)=⊤) :
    Ideal.span (Set.range a)=⊤ := by
  let I := Ideal.span (Set.range a)
  have hb (i : α) : b i ∈ I := by
    have he : b i= -(∑ j : β,A i j*a j) := by linear_combination hzero i
    rw [he]
    apply I.neg_mem
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)
  apply top_unique
  rw [← hfull]
  apply Ideal.span_le.mpr
  rintro x (hx|hx)
  · obtain ⟨i,rfl⟩ := hx
    exact hb i
  · exact Ideal.subset_span hx

/-- Five universal linear equations in forty-five matrix entries leave an actual
polynomial algebra in forty variables, over the original arbitrary coefficient ring. -/
def quotientEquivForty (b : Fin 5 → R) (a : Fin 8 → R) (u : Rˣ) :
    Ring b a u ≃ₐ[R] MvPolynomial (Fin 40) R :=
  (quotientEquiv b a u).trans (MvPolynomial.renameEquiv R finProdFinEquiv)

theorem standardSmoothForty (b : Fin 5 → R) (a : Fin 8 → R) (u : Rˣ) :
    Algebra.IsStandardSmoothOfRelativeDimension 40 R (Ring b a u) :=
  Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 40 (quotientEquivForty b a u).symm

end M9Native.LinearIncidenceElimination

end

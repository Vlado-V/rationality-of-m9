module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The actual ideal of a polynomial graph over any commutative ring.
The inverse on the quotient is constructed by retaining the free variables. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial

universe u v w

namespace M9Native.PolynomialGraphKernel

variable (R : Type u) [CommRing R] (σ : Type v) (τ : Type w)
  (f : σ → MvPolynomial τ R)

def graphEvaluation : MvPolynomial (σ ⊕ τ) R →ₐ[R] MvPolynomial τ R :=
  MvPolynomial.aeval (Sum.elim f MvPolynomial.X)

def graphRelation (i : σ) : MvPolynomial (σ ⊕ τ) R :=
  X (Sum.inl i) - MvPolynomial.rename Sum.inr (f i)

def graphIdeal : Ideal (MvPolynomial (σ ⊕ τ) R) :=
  Ideal.span (Set.range (graphRelation R σ τ f))

theorem graphEvaluation_comp_rename :
    (graphEvaluation R σ τ f).comp (MvPolynomial.rename Sum.inr) =
      AlgHom.id R (MvPolynomial τ R) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [graphEvaluation]

theorem graphEvaluation_relation (i : σ) :
    graphEvaluation R σ τ f (graphRelation R σ τ f i) = 0 := by
  rw [graphRelation, map_sub]
  have h := AlgHom.congr_fun (graphEvaluation_comp_rename R σ τ f) (f i)
  simpa only [graphEvaluation, MvPolynomial.aeval_X, Sum.elim_inl,
    AlgHom.comp_apply, AlgHom.id_apply, sub_eq_zero] using h.symm

theorem graphIdeal_le_ker :
    graphIdeal R σ τ f ≤ RingHom.ker (graphEvaluation R σ τ f).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact graphEvaluation_relation R σ τ f i

def quotientToFree : (MvPolynomial (σ ⊕ τ) R ⧸ graphIdeal R σ τ f) →ₐ[R]
    MvPolynomial τ R :=
  Ideal.Quotient.liftₐ (graphIdeal R σ τ f) (graphEvaluation R σ τ f)
    (fun _ h => graphIdeal_le_ker R σ τ f h)

def freeToQuotient : MvPolynomial τ R →ₐ[R]
    (MvPolynomial (σ ⊕ τ) R ⧸ graphIdeal R σ τ f) :=
  (Ideal.Quotient.mkₐ R (graphIdeal R σ τ f)).comp (MvPolynomial.rename Sum.inr)

theorem freeToQuotient_comp_graphEvaluation :
    (freeToQuotient R σ τ f).comp (graphEvaluation R σ τ f) =
      Ideal.Quotient.mkₐ R (graphIdeal R σ τ f) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
    simp only [AlgHom.comp_apply, graphEvaluation, MvPolynomial.aeval_X, Sum.elim_inl]
    change Ideal.Quotient.mk (graphIdeal R σ τ f) (MvPolynomial.rename Sum.inr (f i)) =
      Ideal.Quotient.mk (graphIdeal R σ τ f) (X (Sum.inl i))
    symm
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨i, rfl⟩)
  | inr j => simp [graphEvaluation, freeToQuotient]

/-- This is an equality of actual ideals, so the quotient retains all
nilpotents and all coefficient-ring structure. -/
theorem ker_graphEvaluation :
    RingHom.ker (graphEvaluation R σ τ f).toRingHom = graphIdeal R σ τ f := by
  apply le_antisymm _ (graphIdeal_le_ker R σ τ f)
  intro F hF
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := AlgHom.congr_fun (freeToQuotient_comp_graphEvaluation R σ τ f) F
  exact h.symm.trans (by
    rw [AlgHom.comp_apply, show graphEvaluation R σ τ f F = 0 from hF, map_zero])

theorem quotientToFree_comp_freeToQuotient :
    (quotientToFree R σ τ f).comp (freeToQuotient R σ τ f) =
      AlgHom.id R (MvPolynomial τ R) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [quotientToFree, freeToQuotient, graphEvaluation]

theorem freeToQuotient_comp_quotientToFree :
    (freeToQuotient R σ τ f).comp (quotientToFree R σ τ f) =
      AlgHom.id R (MvPolynomial (σ ⊕ τ) R ⧸ graphIdeal R σ τ f) := by
  apply Ideal.Quotient.algHom_ext
  exact freeToQuotient_comp_graphEvaluation R σ τ f

def quotientFreeEquiv : (MvPolynomial (σ ⊕ τ) R ⧸ graphIdeal R σ τ f) ≃ₐ[R]
    MvPolynomial τ R :=
  AlgEquiv.ofAlgHom (quotientToFree R σ τ f) (freeToQuotient R σ τ f)
    (quotientToFree_comp_freeToQuotient R σ τ f)
    (freeToQuotient_comp_quotientToFree R σ τ f)

end M9Native.PolynomialGraphKernel

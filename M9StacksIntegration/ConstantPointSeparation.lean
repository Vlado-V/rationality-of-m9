module

public import M9StacksIntegration.TensorEvaluationSeparation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

/-! Reduced finite type algebras are separated by constant points.

The proof uses the actual Hilbert Nullstellensatz: finite type algebras are
Jacobson, and the residue field at a maximal ideal is finite over the base.
Algebraic closedness identifies that residue field with the base field.
Combined with tensor coordinates, this gives separation after every extension
of scalars, without assuming a density theorem after base change.
-/

noncomputable section

open scoped TensorProduct

namespace M9Native.ConstantPointSeparation

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {R : Type v} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]

/-- A scalar-valued algebra point with prescribed maximal kernel, obtained from
the actual finite residue field. -/
theorem exists_algebraHom_ker_eq (m : Ideal R) [m.IsMaximal] :
    ∃ χ : R →ₐ[k] k, RingHom.ker χ.toRingHom = m := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  let e : k ≃ₐ[k] (R ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  let χ : R →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)
  refine ⟨χ, ?_⟩
  ext r
  change e.symm (Ideal.Quotient.mk m r) = 0 ↔ r ∈ m
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact e.symm.map_eq_zero_iff

/-- Actual scalar-valued algebra evaluations detect zero in a reduced finite
type algebra over an algebraically closed field. -/
theorem eq_zero_of_forall_algebraHom_eq_zero [IsReduced R] (r : R)
    (hr : ∀ χ : R →ₐ[k] k, χ r = 0) : r = 0 := by
  let : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hrad : r ∈ (⊥ : Ideal R).radical := by
    rw [Ideal.radical_eq_jacobson, Ideal.jacobson]
    apply Ideal.mem_sInf.mpr
    intro m hm
    let : m.IsMaximal := hm.2
    obtain ⟨χ, hχ⟩ := exists_algebraHom_ker_eq (k := k) m
    rw [← hχ]
    exact hr χ
  simpa only [Ideal.radical_bot_of_isReduced, Ideal.mem_bot] using hrad

/-- The simultaneous evaluation of elements at all constant points is injective. -/
theorem algebraHom_evaluations_injective [IsReduced R] :
    Function.Injective (fun r : R => fun χ : R →ₐ[k] k => χ r) := by
  intro r s hrs
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_algebraHom_eq_zero (k := k)
  intro χ
  simpa only [map_sub, sub_eq_zero] using congrFun hrs χ

variable (E : Type w) [CommRing E] [Algebra k E]

/-- Constant points remain jointly injective on the actual tensor algebra after
any scalar extension.  In particular, the extension field need not be algebraically
closed; indeed the coefficient algebra need not be a field. -/
theorem tensor_evaluations_injective [IsReduced R] :
    Function.Injective (fun t : R ⊗[k] E => fun χ : R →ₐ[k] k =>
      TensorEvaluationSeparation.algebraEvaluate χ t) :=
  TensorEvaluationSeparation.simultaneous_algebraEvaluate_injective
    (fun χ : R →ₐ[k] k => χ)
    (eq_zero_of_forall_algebraHom_eq_zero (k := k))

/-- Equality in the actual scalar extension can be checked at all constant
points, using the literal algebra tensor evaluations. -/
theorem tensor_eq_of_forall_evaluation_eq [IsReduced R]
    {s t : R ⊗[k] E}
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ s =
      TensorEvaluationSeparation.algebraEvaluate χ t) : s = t :=
  tensor_evaluations_injective E (funext h)

/-- The zero form is convenient for coefficients of a rational coaction. -/
theorem tensor_eq_zero_of_forall_evaluation_eq_zero [IsReduced R]
    {t : R ⊗[k] E}
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ t = 0) : t = 0 := by
  apply tensor_eq_of_forall_evaluation_eq E
  simpa only [map_zero] using h

end M9Native.ConstantPointSeparation

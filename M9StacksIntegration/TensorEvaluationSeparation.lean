module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

/-! Separation by constant evaluations after tensoring.

A separating family of linear functionals remains separating after tensoring
with any vector space.  The proof uses actual coordinates in a basis of the
second tensor factor.  In particular, it assumes no density statement after
base change.
-/

noncomputable section

open scoped TensorProduct

namespace M9Native.TensorEvaluationSeparation

universe u v w z

section Linear

variable {k : Type u} [Field k]
variable {R : Type v} [AddCommGroup R] [Module k R]
variable {M : Type w} [AddCommGroup M] [Module k M]

/-- Tensor a scalar-valued functional with the identity, and use the tensor
unit isomorphism. -/
def evaluate (φ : R →ₗ[k] k) : R ⊗[k] M →ₗ[k] M :=
  (TensorProduct.lid k M).toLinearMap ∘ₗ φ.rTensor M

@[simp]
theorem evaluate_tmul (φ : R →ₗ[k] k) (r : R) (m : M) :
    evaluate (M := M) φ (r ⊗ₜ[k] m) = φ r • m := by
  simp [evaluate]

/-- The coefficients of an evaluated tensor are evaluations of its actual
tensor coefficients. -/
theorem coefficient_evaluate {J : Type z} [DecidableEq J] (b : Module.Basis J k M)
    (φ : R →ₗ[k] k) (t : R ⊗[k] M) (j : J) :
    b.repr (evaluate φ t) j =
      φ ((TensorProduct.equivFinsuppOfBasisRight b) t j) := by
  classical
  induction t using TensorProduct.inductionOn with
  | tmul r m =>
      simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- A jointly separating family remains jointly separating after tensoring
with any vector space over the same field. -/
theorem eq_zero_of_forall_evaluate_eq_zero {I : Type z}
    (φ : I → R →ₗ[k] k)
    (hsep : ∀ r : R, (∀ i, φ i r = 0) → r = 0)
    (t : R ⊗[k] M) (ht : ∀ i, evaluate (φ i) t = 0) : t = 0 := by
  classical
  let b := Module.Free.chooseBasis k M
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext j
  change (TensorProduct.equivFinsuppOfBasisRight b) t j = 0
  apply hsep
  intro i
  rw [← coefficient_evaluate b (φ i) t j, ht i]
  simp

/-- The simultaneous actual tensor-evaluation map is injective. -/
theorem simultaneous_evaluate_injective {I : Type z}
    (φ : I → R →ₗ[k] k)
    (hsep : ∀ r : R, (∀ i, φ i r = 0) → r = 0) :
    Function.Injective (fun t : R ⊗[k] M => fun i => evaluate (φ i) t) := by
  intro x y h
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_evaluate_eq_zero φ hsep
  intro i
  simpa only [map_sub, sub_eq_zero] using congrFun h i

end Linear

section Algebra

variable {k : Type u} [Field k]
variable {R : Type v} [CommRing R] [Algebra k R]
variable {E : Type w} [CommRing E] [Algebra k E]

/-- The actual scalar-extension evaluation, sending `r ⊗ e` to `χ(r) • e`. -/
def algebraEvaluate (χ : R →ₐ[k] k) : R ⊗[k] E →ₐ[k] E :=
  (Algebra.TensorProduct.lid k E).toAlgHom.comp
    (Algebra.TensorProduct.map χ (AlgHom.id k E))

@[simp]
theorem algebraEvaluate_tmul (χ : R →ₐ[k] k) (r : R) (e : E) :
    algebraEvaluate (E := E) χ (r ⊗ₜ[k] e) = χ r • e := by
  simp [algebraEvaluate]

theorem algebraEvaluate_toLinearMap (χ : R →ₐ[k] k) :
    (algebraEvaluate (E := E) χ).toLinearMap = evaluate χ.toLinearMap := by
  ext r e
  simp

/-- Algebra-valued tensor evaluations are jointly injective whenever the
original scalar-valued algebra evaluations jointly separate elements.  The
coefficient algebra may be arbitrary, so this applies to every field extension. -/
theorem simultaneous_algebraEvaluate_injective {I : Type z}
    (χ : I → R →ₐ[k] k)
    (hsep : ∀ r : R, (∀ i, χ i r = 0) → r = 0) :
    Function.Injective (fun t : R ⊗[k] E => fun i => algebraEvaluate (χ i) t) := by
  intro x y h
  apply simultaneous_evaluate_injective (M := E) (fun i => (χ i).toLinearMap) hsep
  funext i
  change evaluate (χ i).toLinearMap x = evaluate (χ i).toLinearMap y
  rw [← algebraEvaluate_toLinearMap]
  exact congrFun h i

end Algebra

end M9Native.TensorEvaluationSeparation

module

public import M9StacksIntegration.ConstantPointSeparation
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! Universal algebra identities and rational equality from constant points.

An actual tensor identity gives equality at arbitrary extension-field points.
For rational expressions, a regular denominator permits clearing the locus on
which specialization is undefined.  No extension-field density is a premise.
-/

noncomputable section

open scoped TensorProduct

namespace M9Native.ConstantPointRationalEquality

universe u v w z

variable {k : Type u} [Field k]
variable {R : Type v} [CommRing R] [Algebra k R]
variable {S : Type w} [CommRing S] [Algebra k S]
variable {E : Type z} [CommRing E] [Algebra k E]

/-- Actual specialization at a point in each factor of the tensor algebra. -/
def specialize (σ : R →ₐ[k] E) (η : S →ₐ[k] E) : R ⊗[k] S →ₐ[k] E :=
  Algebra.TensorProduct.lift σ η (fun _ _ => Commute.all _ _)

@[simp]
theorem specialize_tmul (σ : R →ₐ[k] E) (η : S →ₐ[k] E) (r : R) (s : S) :
    specialize σ η (r ⊗ₜ[k] s) = σ r * η s := by
  simp [specialize]

section Density

variable [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]

/-- Every nonzero actual tensor has a nonzero evaluation at a constant point. -/
theorem exists_constant_nonzero_evaluation {d : R ⊗[k] S} (hd : d ≠ 0) :
    ∃ χ : R →ₐ[k] k, TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 := by
  classical
  by_contra h
  apply hd
  apply ConstantPointSeparation.tensor_eq_zero_of_forall_evaluation_eq_zero S
  intro χ
  by_contra hχ
  exact h ⟨χ, hχ⟩

/-- Clearing a regular denominator proves vanishing from the constant points
where that denominator has nonzero evaluation. -/
theorem eq_zero_of_evaluations_eq_zero_on_denominator {p d : R ⊗[k] S}
    (hd : IsRightRegular d)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 →
      TensorEvaluationSeparation.algebraEvaluate χ p = 0) : p = 0 := by
  apply hd
  change p * d = 0 * d
  rw [zero_mul]
  apply ConstantPointSeparation.tensor_eq_zero_of_forall_evaluation_eq_zero S
  intro χ
  rw [map_mul]
  by_cases hχ : TensorEvaluationSeparation.algebraEvaluate χ d = 0
  · simp [hχ]
  · simp [h χ hχ]

/-- Equality on the actual constant points in a regular principal open implies
equality in the original tensor algebra. -/
theorem eq_of_evaluations_eq_on_denominator {p q d : R ⊗[k] S}
    (hd : IsRightRegular d)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 →
      TensorEvaluationSeparation.algebraEvaluate χ p =
      TensorEvaluationSeparation.algebraEvaluate χ q) : p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_evaluations_eq_zero_on_denominator hd
  intro χ hχ
  rw [map_sub, sub_eq_zero]
  exact h χ hχ

/-- Literal cross multiplication for a rational coaction: equality at every
constant point where the denominator is defined forces the universal numerator
identity. -/
theorem eq_mul_denominator_of_constant_cross_eq {n d : R ⊗[k] S}
    (hd : IsRightRegular d) (a : S)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 →
      TensorEvaluationSeparation.algebraEvaluate χ n =
        a * TensorEvaluationSeparation.algebraEvaluate χ d) :
    n = (1 ⊗ₜ[k] a) * d := by
  apply eq_of_evaluations_eq_on_denominator hd
  intro χ hχ
  simpa using h χ hχ

/-- Over the actual integral tensor algebra, nonzero denominators are regular;
no regularity hypothesis needs to be supplied separately. -/
theorem eq_mul_denominator_of_constant_cross_eq_of_ne_zero
    [IsDomain (R ⊗[k] S)] {n d : R ⊗[k] S}
    (hd : d ≠ 0) (a : S)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 →
      TensorEvaluationSeparation.algebraEvaluate χ n =
        a * TensorEvaluationSeparation.algebraEvaluate χ d) :
    n = (1 ⊗ₜ[k] a) * d :=
  eq_mul_denominator_of_constant_cross_eq
    (fun _ _ hxy => mul_right_cancel₀ hd hxy) a h

/-- Fixedness under all constant-point evaluations gives the literal universal
coaction identity for the chosen element. -/
theorem coaction_fixed_of_constant_fixed (ρ : S →ₐ[k] R ⊗[k] S) (a : S)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ (ρ a) = a) :
    ρ a = 1 ⊗ₜ[k] a := by
  apply ConstantPointSeparation.tensor_eq_of_forall_evaluation_eq S
  intro χ
  simpa using h χ

/-- The actual universal coaction is trivial if every constant-point action is
the identity.  No group structure is needed for this algebraic implication. -/
theorem coaction_eq_includeRight (ρ : S →ₐ[k] R ⊗[k] S)
    (h : ∀ χ : R →ₐ[k] k,
      (TensorEvaluationSeparation.algebraEvaluate χ).comp ρ = AlgHom.id k S) :
    ρ = Algebra.TensorProduct.includeRight := by
  ext a
  apply coaction_fixed_of_constant_fixed ρ a
  intro χ
  exact AlgHom.congr_fun (h χ) a

/-- An actual universal coaction identity specializes to every extension-field
point (and even to points over any commutative coefficient algebra). -/
theorem specialize_coaction_fixed (ρ : S →ₐ[k] R ⊗[k] S) (a : S)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ (ρ a) = a)
    (σ : R →ₐ[k] E) (η : S →ₐ[k] E) :
    specialize σ η (ρ a) = η a := by
  rw [coaction_fixed_of_constant_fixed ρ a h]
  simp

end Density

section Rational

variable [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
variable {K : Type w} [Field K] [Algebra k K]

/-- A rational expression constant at all constant points of its domain has
the actual numerator identity, with no base-changed density assumption. -/
theorem numerator_eq_denominator_mul_of_constant_div_eq
    (p d : R ⊗[k] K) (hd : IsRightRegular d) (a : K)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 →
      TensorEvaluationSeparation.algebraEvaluate χ p /
        TensorEvaluationSeparation.algebraEvaluate χ d = a) :
    p = d * (1 ⊗ₜ[k] a) := by
  apply eq_of_evaluations_eq_on_denominator hd
  intro χ hχ
  have hp := (div_eq_iff hχ).mp (h χ hχ)
  simpa [mul_comm] using hp

/-- The genuine numerator identity gives the same rational equality at every
extension-field pair of points wherever the actual denominator is nonzero. -/
theorem specialize_div_eq_of_constant_div_eq
    {E : Type z} [Field E] [Algebra k E]
    (p d : R ⊗[k] K) (hd : IsRightRegular d) (a : K)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 →
      TensorEvaluationSeparation.algebraEvaluate χ p /
        TensorEvaluationSeparation.algebraEvaluate χ d = a)
    (σ : R →ₐ[k] E) (η : K →ₐ[k] E)
    (hσ : specialize σ η d ≠ 0) :
    specialize σ η p / specialize σ η d = η a := by
  apply (div_eq_iff hσ).mpr
  rw [numerator_eq_denominator_mul_of_constant_div_eq p d hd a h, map_mul]
  simp [mul_comm]

/-- The resulting equality is an equality in the actual fraction field of the
tensor algebra, rather than just a pointwise formula. -/
theorem fraction_eq_of_constant_div_eq [IsDomain (R ⊗[k] K)]
    (p d : R ⊗[k] K) (hd : d ≠ 0) (a : K)
    (h : ∀ χ : R →ₐ[k] k,
      TensorEvaluationSeparation.algebraEvaluate χ d ≠ 0 →
      TensorEvaluationSeparation.algebraEvaluate χ p /
        TensorEvaluationSeparation.algebraEvaluate χ d = a) :
    algebraMap (R ⊗[k] K) (FractionRing (R ⊗[k] K)) p /
        algebraMap (R ⊗[k] K) (FractionRing (R ⊗[k] K)) d =
      algebraMap (R ⊗[k] K) (FractionRing (R ⊗[k] K)) (1 ⊗ₜ[k] a) := by
  have hreg : IsRightRegular d := fun _ _ hxy => mul_right_cancel₀ hd hxy
  have hd' : algebraMap (R ⊗[k] K) (FractionRing (R ⊗[k] K)) d ≠ 0 :=
    fun hz => hd (IsFractionRing.injective (R ⊗[k] K)
      (FractionRing (R ⊗[k] K)) (by simpa using hz))
  apply (div_eq_iff hd').mpr
  rw [numerator_eq_denominator_mul_of_constant_div_eq p d hreg a h, map_mul]
  exact mul_comm _ _

end Rational

end M9Native.ConstantPointRationalEquality

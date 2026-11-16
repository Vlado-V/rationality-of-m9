module

public import M9StacksIntegration.NativeAffinePullbackEvaluation
public import M9StacksIntegration.ConstantPointRationalEquality

@[expose] public section

/-! Constant slice identities for an actual dominant native scheme map
force its rational pullback to equal the original tensor coefficient.
The slice identities concern actual generic-image field points.  They do
not assume an identity of universal rational pullbacks or invariance under
arbitrary extension-valued points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace M9Native.NativeTensorInvariantPullback

open NativePullbackFractionEvaluation NativeGenericPullbackEvaluation

variable {X : Scheme} [IsIntegral X]
variable (k : Type) [Field k] [IsAlgClosed k]
variable (A E : Type) [CommRing A] [Algebra k A] [IsReduced A]
    [Algebra.FiniteType k A] [Field E] [Algebra k E]
    [IsDomain (A ⊗[k] E)]

/-- Actual native constant-slice pullbacks determine the actual universal
pullback.  The local-ring comparison remains valid when the chosen
universal denominator vanishes at a particular slice. -/
theorem pullback_eq_coefficient
    (a : Spec (.of (A ⊗[k] E)) ⟶ X) [IsDominant a]
    (ha : ∀ χ : A →ₐ[k] k,
      a (Spec.map (CommRingCat.ofHom
        (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom)
          (IsLocalRing.closedPoint E)) = genericPoint X)
    (f : X.functionField) (c : E)
    (hf : ∀ χ : A →ₐ[k] k,
      pointPullback a (Spec.map (CommRingCat.ofHom
        (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom)) (ha χ) f = c) :
    NativeDominantFunctionField.map a f =
      algebraMap (A ⊗[k] E) (Spec (.of (A ⊗[k] E))).functionField (1 ⊗ₜ[k] c) := by
  let R := A ⊗[k] E
  let F := (Spec (.of R)).functionField
  let : Algebra R F := GrassmannianCharts.affineFunctionField_ringAlgebra R
  let : IsFractionRing R F := GrassmannianCharts.affineFunctionField_isFractionRing R
  obtain ⟨n, d, hdmem, hrep⟩ := IsFractionRing.div_surjective R (NativeDominantFunctionField.map a f)
  have hd : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hdmem
  have hιd : algebraMap R F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdmem
  have hc (χ : A →ₐ[k] k) :
      TensorEvaluationSeparation.algebraEvaluate (E := E) χ n =
        c * TensorEvaluationSeparation.algebraEvaluate (E := E) χ d := by
    have he := NativeAffinePullbackEvaluation.cross_identity_of_fraction_at_affine_point
      R a (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom
      (ha χ) f n d hd hrep.symm
    exact he.symm.trans (congrArg (fun q : E =>
      q * TensorEvaluationSeparation.algebraEvaluate (E := E) χ d) (hf χ))
  have hnd : n = (1 ⊗ₜ[k] c) * d :=
    ConstantPointRationalEquality.eq_mul_denominator_of_constant_cross_eq_of_ne_zero hd c
      (fun χ _ => hc χ)
  calc
    NativeDominantFunctionField.map a f = algebraMap R F n / algebraMap R F d := hrep.symm
    _ = algebraMap R F (1 ⊗ₜ[k] c) := by
      rw [hnd, map_mul, mul_div_cancel_right₀ _ hιd]

end M9Native.NativeTensorInvariantPullback

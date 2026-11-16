module

public import M9StacksIntegration.ConicOrdinaryGraphGeometry

/-! Literal connected and odd changes of the actual ordinary moving graphs. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Matrix
open scoped Classical

namespace M9Native.ConicOrdinaryGraphTransform

open M9.GraphBundleDescent M9.MovingDeterminantFrames
open M9.DeterminantFrameScalarExtension M9.PrimitiveTwistedReduced
open ConicFrameHeadMatrices MovingConicCells ConicConstantActionMatrices
open ConicOrdinaryGraphGeometry ConicCompatibleGraphCoordinates

variable (K : Type*) [Field K] [Algebra ℂ K] [CharZero K]

local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

omit [Algebra ℂ K] [CharZero K] in
theorem kernel_mul_of_covariance {a b c : ℕ}
    (Q : Matrix (Fin b) (Fin a) K) (C : Matrix.GeneralLinearGroup (Fin a) K)
    (E E' : (Fin c → K) →ₗ[K] (Fin a → K))
    (T : Matrix.GeneralLinearGroup (Fin c) K)
    (hQ : LinearMap.ker Q.mulVecLin = LinearMap.range E)
    (hcov : ∀ x, C.val.mulVec (E' x) = E (T.val.mulVec x)) :
    LinearMap.ker (Q * C.val).mulVecLin = LinearMap.range E' := by
  have hCi : Function.Injective C.val.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr C.isUnit
  have hTs : Function.Surjective T.val.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr T.isUnit
  ext v
  change (Q * C.val).mulVec v = 0 ↔ ∃ x, E' x = v
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := (show C.val.mulVec v ∈ LinearMap.range E by rw [← hQ]; exact hv)
    obtain ⟨y, hy⟩ := hTs x
    refine ⟨y, hCi ?_⟩
    rw [hcov, hy, hx]
  · rintro ⟨x, rfl⟩
    rw [hcov]
    exact (show E (T.val.mulVec x) ∈ LinearMap.ker Q.mulVecLin by rw [hQ]; exact ⟨_, rfl⟩)

omit [CharZero K] in
theorem frameMap_mul (F G : GL3 K) (x : Head K) :
    frameMap K (F * G) x = congruenceEquiv K F (frameMap K G x) :=
  congruenceEquiv_mul K F G _

omit [CharZero K] in
theorem frameMap_scalar_mul (a : Kˣ) (F : GL3 K) (x : Head K) :
    frameMap K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) x =
      (a^2).val • frameMap K F x :=
  congruenceEquiv_scalar_mul K a F _

omit [Algebra ℂ K] [CharZero K] in
theorem congruence_inv_cancel (F : GL3 K) (q : M9.Symmetric3 K) :
    congruenceEquiv K F (congruenceEquiv K F⁻¹ q) = q := by
  rw [← congruenceEquiv_mul, mul_inv_cancel]
  exact M9.PrimitiveRepresentation.congruence_one K q

def firstTransform (g : Matrix.SpecialLinearGroup (Fin 3) K) (a : Kˣ) (F : GL3 K) : GL3 K :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) a * ((Matrix.SpecialLinearGroup.toGL g)⁻¹ * F)

def secondTransform (g : Matrix.SpecialLinearGroup (Fin 3) K) (b : Kˣ) (H : GL3 K) : GL3 K :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) b *
    ((Matrix.SpecialLinearGroup.toGL (M9.PrimitiveRepresentation.inverseTranspose K g))⁻¹ * H)

def rawTransform (a b : Kˣ) (Z : GL4 K) : GL4 K :=
  Matrix.GeneralLinearGroup.scalar (Fin 4) (a^2 / b^2) * Z

omit [Algebra ℂ K] [CharZero K] in
theorem scalarUnit_mulVec {n : ℕ} (a : Kˣ) (x : Fin n → K) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) a).val.mulVec x = a.val • x := by
  change (Matrix.scalar (Fin n) a.val).mulVec x = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec]

omit [Algebra ℂ K] [CharZero K] in
theorem rawTransform_mulVec (a b : Kˣ) (Z : GL4 K) (x : Head K) :
    (rawTransform K a b Z).val.mulVec x = (a^2 / b^2).val • Z.val.mulVec x := by
  rw [rawTransform, Units.val_mul, ← Matrix.mulVec_mulVec, scalarUnit_mulVec]

/-- The original connected native representation carries the genuinely
normalised inverse-frame graph to the original graph with its actual scalar. -/
theorem framedEmbedding_connected (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (a b : Kˣ) (F H : GL3 K) (Z : GL4 K) (x : Head K) :
    (matrixRepresentation K (SemidirectProduct.inl g)).val.mulVec
      (framedEmbedding K (firstTransform K g a F) (secondTransform K g b H)
        (rawTransform K a b Z) x) =
      framedEmbedding K F H Z ((a^2).val • x) := by
  change (matrixRepresentation K (SemidirectProduct.inl g)).val.mulVec
    (pairCoordinates K (frameMap K (firstTransform K g a F) x,
      frameMap K (secondTransform K g b H) ((rawTransform K a b Z).val.mulVec x))) = _
  rw [matrixRepresentation_connected_pair]
  apply congrArg (pairCoordinates K)
  apply Prod.ext
  · change congruenceEquiv K (Matrix.SpecialLinearGroup.toGL g)
      (frameMap K (firstTransform K g a F) x) = frameMap K F ((a^2).val • x)
    rw [firstTransform, frameMap_scalar_mul, frameMap_mul, map_smul,
      congruence_inv_cancel, map_smul]
  · change congruenceEquiv K
      (Matrix.SpecialLinearGroup.toGL (M9.PrimitiveRepresentation.inverseTranspose K g))
      (frameMap K (secondTransform K g b H) ((rawTransform K a b Z).val.mulVec x)) =
        frameMap K H (Z.val.mulVec ((a^2).val • x))
    rw [secondTransform, frameMap_scalar_mul, frameMap_mul, map_smul,
      congruence_inv_cancel, rawTransform_mulVec, map_smul, smul_smul,
      Matrix.mulVec_smul, map_smul]
    have hc : (b^2).val * (a^2 / b^2).val = (a^2).val := by
      rw [← Units.val_mul]
      exact congrArg Units.val (show b^2 * (a^2 / b^2) = a^2 by
        simp [div_eq_mul_inv, mul_left_comm])
    rw [hc]

/-- The original odd generator is the literal factor swap with inverse raw map. -/
theorem framedEmbedding_odd (F H : GL3 K) (Z : GL4 K) (x : Head K) :
    (matrixRepresentation K (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)).val.mulVec
      (framedEmbedding K H F Z⁻¹ x) = framedEmbedding K F H Z (Z⁻¹.val.mulVec x) := by
  change (matrixRepresentation K (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)).val.mulVec
    (pairCoordinates K (frameMap K H x, frameMap K F (Z⁻¹.val.mulVec x))) = _
  rw [matrixRepresentation_odd_pair]
  change pairCoordinates K (frameMap K F (Z⁻¹.val.mulVec x), frameMap K H x) =
    pairCoordinates K (frameMap K F (Z⁻¹.val.mulVec x),
      frameMap K H (Z.val.mulVec (Z⁻¹.val.mulVec x)))
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/-- Exact connected native action on the actual ordinary quotient kernels. -/
theorem ordinaryQuotient_connected_kernel (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (a b : Kˣ) (F H : GL3 K) (Z : GL4 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det)
    (hF' : IsUnit (headMatrix K (firstTransform K g a F)).det)
    (hH' : IsUnit (headMatrix K (secondTransform K g b H)).det) :
    LinearMap.ker ((ordinaryQuotient K F H hF hH Z) *
      (matrixRepresentation K (SemidirectProduct.inl g)).val).mulVecLin =
    LinearMap.ker (ordinaryQuotient K (firstTransform K g a F) (secondTransform K g b H)
      hF' hH' (rawTransform K a b Z)).mulVecLin := by
  rw [ordinaryQuotient_kernel K (firstTransform K g a F) (secondTransform K g b H)]
  apply kernel_mul_of_covariance K _ _ (framedEmbedding K F H Z)
    (framedEmbedding K (firstTransform K g a F) (secondTransform K g b H)
      (rawTransform K a b Z)) (Matrix.GeneralLinearGroup.scalar (Fin 4) (a^2))
  · exact ordinaryQuotient_kernel K F H hF hH Z
  · intro x
    rw [scalarUnit_mulVec]
    exact framedEmbedding_connected K g a b F H Z x

/-- Exact odd native action on the actual ordinary quotient kernels. -/
theorem ordinaryQuotient_odd_kernel (F H : GL3 K) (Z : GL4 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det) :
    LinearMap.ker ((ordinaryQuotient K F H hF hH Z) *
      (matrixRepresentation K (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)).val).mulVecLin =
    LinearMap.ker (ordinaryQuotient K H F hH hF Z⁻¹).mulVecLin := by
  rw [ordinaryQuotient_kernel K H F hH hF Z⁻¹]
  exact kernel_mul_of_covariance K _ _ (framedEmbedding K F H Z)
    (framedEmbedding K H F Z⁻¹) Z⁻¹ (ordinaryQuotient_kernel K F H hF hH Z)
    (framedEmbedding_odd K F H Z)

end M9Native.ConicOrdinaryGraphTransform

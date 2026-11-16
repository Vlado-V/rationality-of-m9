module

public import M9.DeterminantFrameScalarEquivariance
public import M9.GraphBundleDescent

/-!
# Constant matrices of the actual raw tensor representation

The complex matrix is obtained by conjugating the literal action on
E₀ with its original tensor-evaluation equivalence. The K-matrix is
its actual coefficient extension. Its action is proved on the original
K ⊗[ℂ] E₀, using the literal raw coordinates and rawGamma maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace M9Native.ConicRawGammaMatrices

open M9.GraphBundleDescent M9.StandardFourPlaneRepresentation
open M9.DeterminantFrameScalarExtension M9.DeterminantFrameScalarEquivariance

abbrev Gamma := M9.TetrahedralGroup.Gamma

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

/-- Matrix of the literal complex representation in the original
actual tensor-evaluation coordinates. -/
def gammaC : Gamma →* GL4 ℂ where
  toFun g := (matrixLinearEquiv ℂ).symm
    (tensorEvaluationEquiv.symm.trans ((tensorRepresentation g).trans tensorEvaluationEquiv))
  map_one' := by
    apply (matrixLinearEquiv ℂ).injective
    simp only [MulEquiv.apply_symm_apply, map_one]
    apply LinearEquiv.ext
    intro v
    change tensorEvaluationEquiv (tensorEvaluationEquiv.symm v) = v
    exact tensorEvaluationEquiv.apply_symm_apply v
  map_mul' g h := by
    apply (matrixLinearEquiv ℂ).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

/-- Actual coefficient extension of the complex matrix representation. -/
def gammaK (K : Type*) [Field K] [Algebra ℂ K] : Gamma →* GL4 K :=
  (Matrix.GeneralLinearGroup.map (algebraMap ℂ K)).comp gammaC

/-- The construction retains the literal original conjugated action. -/
theorem matrixLinearEquiv_gammaC (g : Gamma) :
    matrixLinearEquiv ℂ (gammaC g) =
      tensorEvaluationEquiv.symm.trans ((tensorRepresentation g).trans tensorEvaluationEquiv) :=
  (matrixLinearEquiv ℂ).apply_symm_apply _

/-- The matrix acts by the actual complex tensor representation. -/
theorem gammaC_mulVec_tensorEvaluation (g : Gamma) (x : E0) :
    (gammaC g).val.mulVec (tensorEvaluationEquiv x) =
      tensorEvaluationEquiv (tensorRepresentation g x) := by
  have h := LinearEquiv.congr_fun (matrixLinearEquiv_gammaC g) (tensorEvaluationEquiv x)
  change (gammaC g).val.mulVec (tensorEvaluationEquiv x) = _ at h
  simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h

section Coefficients

variable (K : Type*) [Field K] [Algebra ℂ K]

@[simp] theorem gammaK_apply (g : Gamma) (i j : Fin 4) :
    (gammaK K g).val i j = algebraMap ℂ K ((gammaC g).val i j) := rfl

/-- Coefficient extension commutes with the literal matrix action on
complex constant vectors. -/
theorem gammaK_mulVec_constants (g : Gamma) (v : Fin 4 → ℂ) :
    (gammaK K g).val.mulVec (fun i => algebraMap ℂ K (v i)) =
      fun i => algebraMap ℂ K ((gammaC g).val.mulVec v i) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℂ K) (gammaC g).val v i).symm

private theorem rawCoordinates_tmul_vector (a : K) (x : E0) :
    rawCoordinates K (a ⊗ₜ[ℂ] x) =
      a • (fun i => algebraMap ℂ K (tensorEvaluationEquiv x i)) := by
  funext i
  rw [rawCoordinates_tmul]
  exact mul_comm _ _

/-- The required coordinate law holds on the actual coefficient-extended
original tensor module, with no supplied action or matrix identity. -/
theorem gammaK_mulVec_rawCoordinates (g : Gamma) (x : K ⊗[ℂ] E0) :
    (gammaK K g).val.mulVec (rawCoordinates K x) =
      rawCoordinates K (rawGamma K g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      have hg : rawGamma K g (a ⊗ₜ[ℂ] x) = a ⊗ₜ[ℂ] (tensorRepresentation g x) :=
        LinearEquiv.baseChange_tmul ℂ K E0 E0 (e := tensorRepresentation g) a x
      calc
        (gammaK K g).val.mulVec (rawCoordinates K (a ⊗ₜ[ℂ] x)) =
            (gammaK K g).val.mulVec
              (a • (fun i => algebraMap ℂ K (tensorEvaluationEquiv x i))) :=
          congrArg (gammaK K g).val.mulVec (rawCoordinates_tmul_vector K a x)
        _ = a • (gammaK K g).val.mulVec
              (fun i => algebraMap ℂ K (tensorEvaluationEquiv x i)) :=
          Matrix.mulVec_smul _ a _
        _ = a • (fun i => algebraMap ℂ K ((gammaC g).val.mulVec
              (tensorEvaluationEquiv x) i)) :=
          congrArg (a • ·) (gammaK_mulVec_constants K g (tensorEvaluationEquiv x))
        _ = a • (fun i => algebraMap ℂ K (tensorEvaluationEquiv (tensorRepresentation g x) i)) :=
          congrArg (fun v : Fin 4 → ℂ => a • (fun i => algebraMap ℂ K (v i)))
            (gammaC_mulVec_tensorEvaluation g x)
        _ = rawCoordinates K (a ⊗ₜ[ℂ] (tensorRepresentation g x)) :=
          (rawCoordinates_tmul_vector K a (tensorRepresentation g x)).symm
        _ = rawCoordinates K (rawGamma K g (a ⊗ₜ[ℂ] x)) :=
          congrArg (rawCoordinates K) hg.symm
  | add x y hx hy =>
      calc
        (gammaK K g).val.mulVec (rawCoordinates K (x+y)) =
            (gammaK K g).val.mulVec (rawCoordinates K x + rawCoordinates K y) :=
          congrArg (gammaK K g).val.mulVec ((rawCoordinates K).map_add x y)
        _ = (gammaK K g).val.mulVec (rawCoordinates K x) +
              (gammaK K g).val.mulVec (rawCoordinates K y) :=
          Matrix.mulVec_add _ _ _
        _ = rawCoordinates K (rawGamma K g x) + rawCoordinates K (rawGamma K g y) :=
          congrArg₂ (· + ·) hx hy
        _ = rawCoordinates K (rawGamma K g x + rawGamma K g y) :=
          ((rawCoordinates K).map_add _ _).symm
        _ = rawCoordinates K (rawGamma K g (x+y)) :=
          congrArg (rawCoordinates K) ((rawGamma K g).map_add x y).symm

/-- The coefficients remain the original complex constants under every
actual complex-algebra coefficient homomorphism. -/
theorem map_gammaK {L : Type*} [Field L] [Algebra ℂ L] (φ : K →ₐ[ℂ] L) (g : Gamma) :
    Matrix.GeneralLinearGroup.map φ.toRingHom (gammaK K g) = gammaK L g := by
  apply Units.ext
  ext i j
  change φ (algebraMap ℂ K ((gammaC g).val i j)) =
    algebraMap ℂ L ((gammaC g).val i j)
  exact φ.commutes _

end Coefficients

@[simp] theorem gammaK_complex (g : Gamma) : gammaK ℂ g = gammaC g := by
  apply Units.ext
  ext i j
  rfl

end M9Native.ConicRawGammaMatrices

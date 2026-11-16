module

public import M9.DeterminantFrameScalarExtension

/-!
# Literal Gamma transitions after scalar extension

The actual constant Gamma matrices preserve the actual scalar-extended plane.
Its actual tensor/exterior-dual action is the scalar extension of the frozen
complex E0 representation, through the coefficient-preserving comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
open scoped Classical TensorProduct Matrix

namespace M9.DeterminantFrameScalarEquivariance
open Module StandardFourPlaneRepresentation MovingDeterminantFrames
open DeterminantFrameScalarExtension TetrahedralGroup

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

variable (K : Type*) [Field K] [Algebra ℂ K]

local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

/-- Coefficient extension commutes with the literal symmetric-square matrix
action, on every original pure tensor. -/
theorem symmetricBaseChangeEquiv_congruence_tmul (M : Matrix (Fin 3) (Fin 3) ℂ)
    (a : K) (q : M9.Symmetric3 ℂ) :
    symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] PrimitiveRepresentation.congruence ℂ M q) =
      PrimitiveRepresentation.congruence K (M.map (algebraMap ℂ K))
        (symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] q)) := by
  apply Subtype.ext
  ext i j
  rw [symmetricBaseChangeEquiv_tmul_entry]
  simp only [PrimitiveRepresentation.congruence_val, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    symmetricBaseChangeEquiv_tmul_entry, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- The original actual Gamma matrix, with its coefficients included in K. -/
def constantGamma (g : Gamma) : GL3 K :=
  Matrix.GeneralLinearGroup.map (algebraMap ℂ K) (FrameAction.tetrahedralGL g)

/-- The actual scalar extension of the actual restricted Gamma action. -/
def scalarGamma (g : Gamma) : standardPlane K ≃ₗ[K] standardPlane K :=
  ((standardPlaneFrame K).symm.trans
    ((gammaActionEquiv g).baseChange ℂ K S0 S0)).trans (standardPlaneFrame K)

@[simp] theorem scalarGamma_frame_tmul (g : Gamma) (a : K) (q : S0) :
    scalarGamma K g (standardPlaneFrame K (a ⊗ₜ[ℂ] q)) =
      standardPlaneFrame K (a ⊗ₜ[ℂ] gammaActionEquiv g q) := by
  simp only [scalarGamma, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.baseChange_tmul]

theorem scalarGamma_val (g : Gamma) (q : standardPlane K) :
    (scalarGamma K g q).val = congruenceEquiv K (constantGamma K g) q.val := by
  obtain ⟨x,rfl⟩ := (standardPlaneFrame K).surjective q
  induction x using TensorProduct.inductionOn with
  | tmul a q =>
      rw [scalarGamma_frame_tmul]
      change symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] (gammaActionEquiv g q).val) = _
      exact symmetricBaseChangeEquiv_congruence_tmul K (matrix g) a q.val
  | add x y hx hy =>
      simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy

/-- Literal constant Gamma congruence preserves the literal embedded K-plane. -/
theorem constantGamma_plane (g : Gamma) :
    movingPlane K (standardPlane K) (constantGamma K g) = standardPlane K := by
  ext q
  constructor
  · rintro ⟨v,hv,rfl⟩
    change congruenceEquiv K (constantGamma K g) v ∈ standardPlane K
    rw [← scalarGamma_val K g ⟨v,hv⟩]
    exact (scalarGamma K g ⟨v,hv⟩).property
  · intro hq
    let v := (scalarGamma K g).symm ⟨q,hq⟩
    refine ⟨v.val,v.property,?_⟩
    change congruenceEquiv K (constantGamma K g) v.val = q
    rw [← scalarGamma_val]
    exact congrArg Subtype.val ((scalarGamma K g).apply_symm_apply ⟨q,hq⟩)

theorem constantGamma_stabilizer (g : Gamma) :
    stabilizerAction K (standardPlane K) (constantGamma K g) (constantGamma_plane K g) =
      scalarGamma K g := by
  apply LinearEquiv.ext
  intro q
  apply Subtype.ext
  exact (scalarGamma_val K g q).symm

@[simp] theorem constantGamma_det (g : Gamma) :
    Matrix.GeneralLinearGroup.det (constantGamma K g) = 1 := by
  rw [constantGamma, Matrix.GeneralLinearGroup.map_det]
  have hd : Matrix.GeneralLinearGroup.det (FrameAction.tetrahedralGL g) = 1 := by
    apply Units.ext
    exact matrix_det g
  rw [hd, map_one]

@[simp] theorem scalarGamma_baseVector (g : Gamma) (q : S0) :
    scalarGamma K g (baseVector K q) = baseVector K (gammaActionEquiv g q) :=
  scalarGamma_frame_tmul K g 1 q

@[simp] theorem scalarGamma_symm_baseVector (g : Gamma) (q : S0) :
    (scalarGamma K g).symm (baseVector K q) = baseVector K ((gammaActionEquiv g).symm q) := by
  apply (scalarGamma K g).injective
  rw [LinearEquiv.apply_symm_apply, scalarGamma_baseVector, LinearEquiv.apply_symm_apply]

theorem standardPlaneBasis_eq_baseVector (i : Fin 4) :
    standardPlaneBasis K i = baseVector K (evaluationBasis i) := by
  simp only [standardPlaneBasis, Basis.map_apply, Basis.baseChange_apply, baseVector]

/-- Actual dual-exterior transport commutes with the original coefficient
extension on every actual top form. -/
theorem scalarExtendedDual_gamma (g : Gamma)
    (φ : StandardFourPlaneRepresentation.DeterminantDual) :
    determinantDualTransport (scalarGamma K g) (scalarExtendedDual K φ) =
      scalarExtendedDual K (determinantDualAction g φ) := by
  apply (MovingDeterminantFrames.determinantDualCoordinates (standardPlaneBasis K)).injective
  rw [MovingDeterminantFrames.determinantDualCoordinates_apply,
    MovingDeterminantFrames.determinantDualCoordinates_apply,
    determinantDualTransport_apply, exteriorPower.map_apply_ιMulti]
  have hb : standardPlaneBasis K = fun i => baseVector K (evaluationBasis i) := by
    funext i
    exact standardPlaneBasis_eq_baseVector K i
  rw [hb]
  have hh : (scalarGamma K g).symm.toLinearMap ∘ (fun i => baseVector K (evaluationBasis i)) =
      fun i => baseVector K ((gammaActionEquiv g).symm (evaluationBasis i)) := by
    funext i
    exact scalarGamma_symm_baseVector K g (evaluationBasis i)
  rw [hh, scalarExtendedDual_eval, scalarExtendedDual_eval]
  change algebraMap ℂ K (φ (exteriorPower.ιMulti ℂ 4
      (fun i => (gammaActionEquiv g).symm (evaluationBasis i)))) =
    algebraMap ℂ K (φ (exteriorPower.map 4 (gammaActionEquiv g).symm.toLinearMap
      (exteriorPower.ιMulti ℂ 4 evaluationBasis)))
  rw [exteriorPower.map_apply_ιMulti]
  rfl

/-- The literal coefficient extension of the actual complex tensor action. -/
def rawGamma (g : Gamma) : (K ⊗[ℂ] E0) ≃ₗ[K] (K ⊗[ℂ] E0) :=
  (tensorRepresentation g).baseChange ℂ K E0 E0

/-- The coefficient-preserving scalar extension equivalence intertwines the
actual complex E0 representation with the actual tensor/exterior action. -/
theorem rawToTwisted_gamma (g : Gamma) (x : K ⊗[ℂ] E0) :
    rawToTwisted K (rawGamma K g x) =
      tensorTransport (scalarGamma K g) (rawToTwisted K x) := by
  let f : (K ⊗[ℂ] E0) →ₗ[K] Twisted K (standardPlane K) :=
    (rawToTwisted K).toLinearMap.comp (rawGamma K g).toLinearMap
  let h : (K ⊗[ℂ] E0) →ₗ[K] Twisted K (standardPlane K) :=
    (tensorTransport (scalarGamma K g)).toLinearMap.comp (rawToTwisted K).toLinearMap
  have he : f.restrictScalars ℂ = h.restrictScalars ℂ := by
    apply TensorProduct.ext_threefold'
    intro a q φ
    change rawToTwisted K (a ⊗ₜ[ℂ]
      (gammaActionEquiv g q ⊗ₜ[ℂ] determinantDualAction g φ)) =
      tensorTransport (scalarGamma K g) (rawToTwisted K (a ⊗ₜ[ℂ] (q ⊗ₜ[ℂ] φ)))
    rw [rawToTwisted_tmul_tmul, rawToTwisted_tmul_tmul,
      tensorTransport_tmul, scalarGamma_frame_tmul, scalarExtendedDual_gamma]
  exact LinearMap.congr_fun he x

theorem rawToTwisted_gamma_tmul (g : Gamma) (a : K) (x : E0) :
    rawToTwisted K (rawGamma K g (a ⊗ₜ[ℂ] x)) =
      tensorTransport (scalarGamma K g) (rawToTwisted K (a ⊗ₜ[ℂ] x)) :=
  rawToTwisted_gamma K g (a ⊗ₜ[ℂ] x)

theorem rawToTwisted_conjugate (g : Gamma) :
    (rawGamma K g).trans (rawToTwisted K) =
      (rawToTwisted K).trans (tensorTransport (scalarGamma K g)) := by
  apply LinearEquiv.ext
  exact rawToTwisted_gamma K g

/-- The actual normalized moving-plane frame, with source exactly the
coefficient-extended E0 used by finite Galois descent. -/
def rawMovingFrame (F : GL3 K) :
    (K ⊗[ℂ] E0) ≃ₗ[K] Twisted K (movingPlane K (standardPlane K) F) :=
  (rawToTwisted K).trans (compensatedFrame K (standardPlane K) F)

/-- A genuine right-deck compatibility on the original scalar-extended
tensor source and the actual moving determinant-tensor target. -/
theorem rawMovingFrame_right_gamma (g : Gamma) (F : GL3 K) :
    (rawMovingFrame K (F * constantGamma K g)).trans
        (tensorTransport (planeEquivOfEq K (movingPlane_right K (standardPlane K)
          (constantGamma K g) F (constantGamma_plane K g)))) =
      (rawGamma K g).trans (rawMovingFrame K F) := by
  have ht := compensatedFrame_right K (standardPlane K) (constantGamma K g) F
    (constantGamma_plane K g) (constantGamma_det K g)
  rw [constantGamma_stabilizer] at ht
  apply LinearEquiv.ext
  intro x
  have hp := LinearEquiv.congr_fun ht (rawToTwisted K x)
  change _ = compensatedFrame K (standardPlane K) F
    (rawToTwisted K (rawGamma K g x))
  rw [rawToTwisted_gamma]
  exact hp

end M9.DeterminantFrameScalarEquivariance

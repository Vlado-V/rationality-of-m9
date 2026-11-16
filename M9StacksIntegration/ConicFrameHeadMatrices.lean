module

public import M9StacksIntegration.ConicCompatibleGraphCoordinates
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Actual conic-compatible head coordinates on the standard four-plane and
on its moving frames. The standard head projection is an isomorphism, not an
assumed generic rank condition. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Matrix
open scoped TensorProduct

namespace M9Native.ConicFrameHeadMatrices

open ConicCompatibleGraphCoordinates M9.GraphBundleDescent
open M9.DeterminantFrameScalarExtension M9.MovingDeterminantFrames

variable (K : Type*) [Field K] [Algebra ℂ K]

/-- The actual equal-diagonal plane over the coefficient field. -/
def equalDiagonalPlane : Submodule K (M9.Symmetric3 K) :=
  LinearMap.ker ((Matrix.toLin' (ConicFrame.standardQuotient : Matrix (Fin 2) (Fin 6) K)).comp
    (conicCoordinates K).toLinearMap)

omit [Algebra ℂ K] in
theorem mem_equalDiagonalPlane (Q : M9.Symmetric3 K) : Q ∈ equalDiagonalPlane K ↔
    Q.val 0 0 = Q.val 1 1 ∧ Q.val 1 1 = Q.val 2 2 := by
  change (ConicFrame.standardQuotient : Matrix (Fin 2) (Fin 6) K).mulVec (conicCoordinates K Q) = 0 ↔ _
  rw [ConicFrame.standardQuotient_kernel]
  rfl

/-- Actual head (22,01,02,12) gives coordinates on the whole equal-diagonal plane. -/
def equalDiagonalHead : equalDiagonalPlane K ≃ₗ[K] Head K where
  toFun Q := (conicSplit K Q.val).1
  invFun x := ⟨⟨ConicFrame.symMatrix ![x 0,x 0,x 0,x 1,x 2,x 3],
      ConicFrame.symMatrix_transpose _⟩, by
    rw [mem_equalDiagonalPlane]
    exact ⟨rfl,rfl⟩⟩
  left_inv Q := by
    apply Subtype.ext
    apply (conicCoordinates K).injective
    have hQ := (mem_equalDiagonalPlane K Q.val).mp Q.property
    change ConicFrame.symCoordinates (ConicFrame.symMatrix
      ![(conicSplit K Q.val).1 0,(conicSplit K Q.val).1 0,(conicSplit K Q.val).1 0,
        (conicSplit K Q.val).1 1,(conicSplit K Q.val).1 2,(conicSplit K Q.val).1 3]) =
      ConicFrame.symCoordinates Q.val.val
    rw [ConicFrame.symCoordinates_symMatrix]
    funext i
    fin_cases i
    · exact (hQ.1.trans hQ.2).symm
    · exact hQ.2.symm
    · rfl
    · rfl
    · rfl
    · rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' Q R := by
    change (conicSplit K (Q.val + R.val)).1 = _
    rw [map_add]
    rfl
  map_smul' c Q := by
    change (conicSplit K (c • Q.val)).1 = _
    rw [map_smul]
    rfl

/-- The scalar-extended original S0 is exactly this actual equal-diagonal plane. -/
theorem standardPlane_eq_equalDiagonal : standardPlane K = equalDiagonalPlane K := by
  have hle : standardPlane K ≤ equalDiagonalPlane K := by
    rintro Q ⟨v,rfl⟩
    induction v using TensorProduct.inductionOn with
    | tmul a q =>
      rw [mem_equalDiagonalPlane]
      constructor
      · change (standardPlaneFrame K (a ⊗ₜ[ℂ] q)).val.val 0 0 =
          (standardPlaneFrame K (a ⊗ₜ[ℂ] q)).val.val 1 1
        rw [standardPlaneFrame_tmul_entry, standardPlaneFrame_tmul_entry]
        exact congrArg (fun c : ℂ => algebraMap ℂ K c * a) q.property.1
      · change (standardPlaneFrame K (a ⊗ₜ[ℂ] q)).val.val 1 1 =
          (standardPlaneFrame K (a ⊗ₜ[ℂ] q)).val.val 2 2
        rw [standardPlaneFrame_tmul_entry, standardPlaneFrame_tmul_entry]
        exact congrArg (fun c : ℂ => algebraMap ℂ K c * a) q.property.2
    | add x y hx hy =>
      rw [map_add]
      exact (equalDiagonalPlane K).add_mem hx hy
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [(standardPlaneBasis K).equivFun.finrank_eq, (equalDiagonalHead K).finrank_eq]

def standardHeadEquiv : standardPlane K ≃ₗ[K] Head K :=
  (LinearEquiv.ofEq _ _ (standardPlane_eq_equalDiagonal K)).trans (equalDiagonalHead K)

def headProjection : M9.Symmetric3 K →ₗ[K] Head K :=
  (LinearMap.fst K (Head K) (Tail K)).comp (conicSplit K).toLinearMap

def tailProjection : M9.Symmetric3 K →ₗ[K] Tail K :=
  (LinearMap.snd K (Head K) (Tail K)).comp (conicSplit K).toLinearMap

def headLinear (F : GL3 K) : Head K →ₗ[K] Head K :=
  (headProjection K).comp ((congruenceEquiv K F).toLinearMap.comp
    ((standardPlane K).subtype.comp (standardPlaneBasis K).equivFun.symm.toLinearMap))

def tailLinear (F : GL3 K) : Head K →ₗ[K] Tail K :=
  (tailProjection K).comp ((congruenceEquiv K F).toLinearMap.comp
    ((standardPlane K).subtype.comp (standardPlaneBasis K).equivFun.symm.toLinearMap))

def headMatrix (F : GL3 K) : Matrix (Fin 4) (Fin 4) K := LinearMap.toMatrix' (headLinear K F)
def tailMatrix (F : GL3 K) : BaseMatrix K := LinearMap.toMatrix' (tailLinear K F)

theorem headMatrix_apply (F : GL3 K) (i j : Fin 4) : headMatrix K F i j =
    (conicSplit K (congruenceEquiv K F (standardPlaneBasis K j).val)).1 i := by
  rw [headMatrix, LinearMap.toMatrix'_apply]
  change (conicSplit K (congruenceEquiv K F
    ((standardPlaneBasis K).equivFun.symm (Pi.single j 1)).val)).1 i = _
  rw [Basis.equivFun_symm_single]

theorem tailMatrix_apply (F : GL3 K) (i : Fin 2) (j : Fin 4) : tailMatrix K F i j =
    (conicSplit K (congruenceEquiv K F (standardPlaneBasis K j).val)).2 i := by
  rw [tailMatrix, LinearMap.toMatrix'_apply]
  change (conicSplit K (congruenceEquiv K F
    ((standardPlaneBasis K).equivFun.symm (Pi.single j 1)).val)).2 i = _
  rw [Basis.equivFun_symm_single]

theorem standardPlaneBasis_entry (j : Fin 4) (r s : Fin 3) :
    (standardPlaneBasis K j).val.val r s = algebraMap ℂ K
      ((M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val r s) := by
  rw [standardPlaneBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    standardPlaneFrame_tmul_entry, mul_one]

/-- Literal quadratic coefficient matrices, valid before any frame inverse is used. -/
def headCoefficients (F : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 4) (Fin 4) K := fun i j =>
  ConicFrame.symCoordinates (F *
    ((M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ K)) *
      F.transpose) (Fin.natAdd 2 i)

def tailCoefficients (F : Matrix (Fin 3) (Fin 3) K) : BaseMatrix K := fun i j =>
  ConicFrame.symCoordinates (F *
    ((M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ K)) *
      F.transpose) (Fin.castAdd 4 i)

theorem headMatrix_eq_coefficients (F : GL3 K) : headMatrix K F = headCoefficients K F.val := by
  ext i j
  rw [headMatrix_apply]
  change (splitSix K (conicCoordinates K
    (congruenceEquiv K F (standardPlaneBasis K j).val))).1 i = _
  rw [splitSix_head]
  change ConicFrame.symCoordinates (F.val * (standardPlaneBasis K j).val.val * F.val.transpose)
    (Fin.natAdd 2 i) = _
  have hQ : (standardPlaneBasis K j).val.val =
      (M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ K) := by
    ext r s
    exact standardPlaneBasis_entry K j r s
  rw [hQ]
  rfl

theorem tailMatrix_eq_coefficients (F : GL3 K) : tailMatrix K F = tailCoefficients K F.val := by
  ext i j
  rw [tailMatrix_apply]
  change (splitSix K (conicCoordinates K
    (congruenceEquiv K F (standardPlaneBasis K j).val))).2 i = _
  rw [splitSix_tail]
  change ConicFrame.symCoordinates (F.val * (standardPlaneBasis K j).val.val * F.val.transpose)
    (Fin.castAdd 4 i) = _
  have hQ : (standardPlaneBasis K j).val.val =
      (M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ K) := by
    ext r s
    exact standardPlaneBasis_entry K j r s
  rw [hQ]
  rfl

def headOneEquiv : Head K ≃ₗ[K] Head K :=
  (standardPlaneBasis K).equivFun.symm.trans (standardHeadEquiv K)

theorem headLinear_one : headLinear K 1 = (headOneEquiv K).toLinearMap := by
  apply LinearMap.ext
  intro x
  change (conicSplit K (M9.PrimitiveRepresentation.congruence K 1
    ((standardPlaneBasis K).equivFun.symm x).val)).1 = _
  rw [M9.PrimitiveRepresentation.congruence_one]
  rfl

def headOneGL : Matrix.GeneralLinearGroup (Fin 4) K :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv (headOneEquiv K))

theorem headMatrix_one_eq_unit : headMatrix K 1 = (headOneGL K).val := by
  apply Matrix.toLin'.injective
  rw [headMatrix, Matrix.toLin'_toMatrix', headLinear_one]
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (headOneEquiv K))
  exact (congrArg (fun f : LinearMap.GeneralLinearGroup K (Head K) =>
    (f : Module.End K (Head K))) h).symm

theorem headCoefficients_one_det_unit : IsUnit (headCoefficients K 1).det := by
  have h : headMatrix K 1 = headCoefficients K (1 : Matrix (Fin 3) (Fin 3) K) := by
    simpa only [Units.val_one] using headMatrix_eq_coefficients K (1 : GL3 K)
  rw [← h, headMatrix_one_eq_unit]
  exact (Matrix.GeneralLinearGroup.det (headOneGL K)).isUnit

end M9Native.ConicFrameHeadMatrices

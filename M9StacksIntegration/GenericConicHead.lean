module

public import M9StacksIntegration.ConicFrameHeadMatrices
public import M9StacksIntegration.ConicFrameRationalGamma

/-! Literal moving-frame coefficient matrices over the actual normalized
conic frame field. Their generic invertibility is proved by evaluation at
the identity and the actual standard-plane head isomorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Matrix

namespace M9Native.GenericConicHead

open M9.GraphBundleDescent ConicFrameHeadMatrices

section Coefficients
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

def literalHead (F : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 4) (Fin 4) R := fun i j =>
  ConicFrame.symCoordinates (F *
    ((M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ R)) *
      F.transpose) (Fin.natAdd 2 i)

def literalTail (F : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 4) R := fun i j =>
  ConicFrame.symCoordinates (F *
    ((M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ R)) *
      F.transpose) (Fin.castAdd 4 i)

theorem literalHead_map (φ : R →ₐ[ℂ] S) (F : Matrix (Fin 3) (Fin 3) R) :
    (literalHead F).map φ.toRingHom = literalHead (F.map φ.toRingHom) := by
  ext i j
  change φ.toRingHom (ConicFrame.symCoordinates (F * _ * F.transpose) (Fin.natAdd 2 i)) = _
  rw [← ConicFrame.symCoordinates_map φ.toRingHom, Matrix.map_mul, Matrix.map_mul]
  have hc : ((M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ R)).map
      φ.toRingHom = (M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ S) := by
    ext a b
    exact φ.commutes _
  rw [hc]
  rfl

theorem literalTail_map (φ : R →ₐ[ℂ] S) (F : Matrix (Fin 3) (Fin 3) R) :
    (literalTail F).map φ.toRingHom = literalTail (F.map φ.toRingHom) := by
  ext i j
  change φ.toRingHom (ConicFrame.symCoordinates (F * _ * F.transpose) (Fin.castAdd 4 i)) = _
  rw [← ConicFrame.symCoordinates_map φ.toRingHom, Matrix.map_mul, Matrix.map_mul]
  have hc : ((M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ R)).map
      φ.toRingHom = (M9.StandardFourPlaneRepresentation.evaluationBasis j).val.val.map (algebraMap ℂ S) := by
    ext a b
    exact φ.commutes _
  rw [hc]
  rfl

end Coefficients

abbrev P := ConicFrameProjective.polynomial ℂ
abbrev L := ConicFrameRationalGamma.L

def headPolynomial : Matrix (Fin 4) (Fin 4) P := literalHead (ConicFrameProjective.normalizedFrame ℂ)
def tailPolynomial : Matrix (Fin 2) (Fin 4) P := literalTail (ConicFrameProjective.normalizedFrame ℂ)

def identityEval : P →ₐ[ℂ] ℂ := MvPolynomial.aeval (ConicFrameCoordinates.identityCoefficients ℂ)

theorem normalizedFrame_identity :
    (ConicFrameProjective.normalizedFrame ℂ).map identityEval.toRingHom = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ConicFrameProjective.normalizedFrame, identityEval, ConicFrameCoordinates.identityCoefficients]

theorem headPolynomial_identity : headPolynomial.map identityEval.toRingHom = literalHead (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [headPolynomial, literalHead_map, normalizedFrame_identity]

/-- The nonzero generic head determinant comes from an actual isomorphism at I. -/
theorem headPolynomial_det_ne_zero : headPolynomial.det ≠ 0 := by
  intro h
  have he := congrArg identityEval h
  rw [map_zero, AlgHom.map_det] at he
  change (headPolynomial.map identityEval.toRingHom).det = 0 at he
  rw [headPolynomial_identity] at he
  exact (headCoefficients_one_det_unit ℂ).ne_zero he

def genericFrameUnit : Matrix.GeneralLinearGroup (Fin 3) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ConicFrameRationalGamma.genericFrame (by
    rw [ConicFrameRationalGamma.genericFrame, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa only [map_zero] using (IsFractionRing.injective P L).ne
      (ConicFrameProjective.normalizedFrame_det_ne_zero ℂ))

def genericHead : Matrix (Fin 4) (Fin 4) L := literalHead ConicFrameRationalGamma.genericFrame
def genericTail : Matrix (Fin 2) (Fin 4) L := literalTail ConicFrameRationalGamma.genericFrame

theorem genericHead_eq_polynomial : genericHead = headPolynomial.map (algebraMap P L) := by
  have h := literalHead_map (IsScalarTower.toAlgHom ℂ P L) (ConicFrameProjective.normalizedFrame ℂ)
  exact h.symm

theorem genericTail_eq_polynomial : genericTail = tailPolynomial.map (algebraMap P L) := by
  have h := literalTail_map (IsScalarTower.toAlgHom ℂ P L) (ConicFrameProjective.normalizedFrame ℂ)
  exact h.symm

theorem genericHead_det_ne_zero : genericHead.det ≠ 0 := by
  rw [genericHead_eq_polynomial, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa only [map_zero] using (IsFractionRing.injective P L).ne headPolynomial_det_ne_zero

def genericHeadUnit : Matrix.GeneralLinearGroup (Fin 4) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero genericHead genericHead_det_ne_zero

/-- Literal actual four-plane big-cell matrix, obtained by solving the head frame. -/
def genericPlaneMatrix : BaseMatrix L := genericTail * (genericHeadUnit)⁻¹.val

/-- Literal determinant-compensated tensor-frame coefficient matrix. -/
def genericCompensatedFrame : Matrix.GeneralLinearGroup (Fin 4) L :=
  Matrix.GeneralLinearGroup.scalar (Fin 4) ((Matrix.GeneralLinearGroup.det genericFrameUnit)^2) *
    adjustedFrameHom L genericHeadUnit

theorem genericHead_actual : headMatrix L genericFrameUnit = genericHead := by
  rw [headMatrix_eq_coefficients]
  rfl

theorem genericTail_actual : tailMatrix L genericFrameUnit = genericTail := by
  rw [tailMatrix_eq_coefficients]
  rfl

end M9Native.GenericConicHead

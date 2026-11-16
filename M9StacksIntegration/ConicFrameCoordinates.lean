module

public import M9StacksIntegration.ConicFrameProjective
public import M9StacksIntegration.JacobianIndependence
public import M9StacksIntegration.FractionDerivation
public import M9StacksIntegration.ConicFrameBaseChange

/-! Literal affine Grassmannian coordinates of the conic-frame map, and
their actual Jacobian at the identity frame. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace M9Native.ConicFrameCoordinates

open MvPolynomial M9Native.ConicFrame M9Native.ConicFrameProjective

variable (K : Type*) [Field K]

def pivot : Matrix (Fin 2) (Fin 2) (polynomial K) :=
  (quotientMatrix (normalizedFrame K)).submatrix id (Fin.castLEEmb (by decide : 2 ≤ 6))

def denominator : polynomial K := (pivot K).det

def numeratorMatrix : Matrix (Fin 2) (Fin 6) (polynomial K) :=
  (pivot K).adjugate * quotientMatrix (normalizedFrame K)

def coordinatePair (j : Fin 8) : Fin 4 × Fin 2 :=
  (finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin (4 * 2)).symm j

def numerator (j : Fin 8) : polynomial K :=
  numeratorMatrix K (coordinatePair j).2 (Fin.natAdd 2 (coordinatePair j).1)

def identityCoefficients : Fin 8 → K := ![0,0,0,1,0,0,0,1]
def atIdentity : polynomial K →+* K := MvPolynomial.eval (identityCoefficients K)

@[simp] theorem normalizedFrame_atIdentity :
    (normalizedFrame K).map (atIdentity K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normalizedFrame,atIdentity,identityCoefficients]

@[simp] theorem denominator_atIdentity : atIdentity K (denominator K) = 1 := by
  norm_num [denominator,pivot,quotientMatrix,congruence,symCoordinates,symMatrix,
    normalizedFrame,Matrix.adjugate_fin_three,standardQuotient,Matrix.det_fin_two,
    Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,Pi.single_apply,atIdentity,identityCoefficients]

theorem denominator_ne_zero : denominator K ≠ 0 := by
  intro h
  have := denominator_atIdentity K
  rw [h,map_zero] at this
  exact zero_ne_one this

def jacobianNumerator : Matrix (Fin 8) (Fin 8) (polynomial K) := fun i j =>
  denominator K * pderiv i (numerator K j) - numerator K j * pderiv i (denominator K)

/-- Evaluation of a polynomial and its actual partial derivative in the dual numbers. -/
def atIdentityDual (i : Fin 8) : polynomial K →+* TrivSqZeroExt K K where
  toFun p := ⟨atIdentity K p,atIdentity K (pderiv i p)⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' p q := by ext <;> simp
  map_mul' p q := by ext <;> simp [Derivation.leibniz,mul_comm]

def dualFrame (i : Fin 8) : Mat3 (TrivSqZeroExt K K) :=
  (normalizedFrame K).map (atIdentityDual K i)

def dualPivot (i : Fin 8) : Matrix (Fin 2) (Fin 2) (TrivSqZeroExt K K) :=
  (quotientMatrix (dualFrame K i)).submatrix id (Fin.castLEEmb (by decide : 2 ≤ 6))

theorem pivot_dual (i : Fin 8) : (pivot K).map (atIdentityDual K i) = dualPivot K i := by
  rw [pivot,← Matrix.submatrix_map,quotientMatrix_map]
  rfl

theorem denominator_dual (i : Fin 8) :
    atIdentityDual K i (denominator K) = (dualPivot K i).det := by
  rw [denominator,RingHom.map_det,RingHom.mapMatrix_apply,pivot_dual]

theorem numerator_dual (i j : Fin 8) :
    atIdentityDual K i (numerator K j) =
      ((dualPivot K i).adjugate * quotientMatrix (dualFrame K i))
        (coordinatePair j).2 (Fin.natAdd 2 (coordinatePair j).1) := by
  have hM : (numeratorMatrix K).map (atIdentityDual K i) =
      (dualPivot K i).adjugate * quotientMatrix (dualFrame K i) := by
    rw [numeratorMatrix,Matrix.map_mul,← RingHom.mapMatrix_apply,
      RingHom.map_adjugate,RingHom.mapMatrix_apply,pivot_dual,quotientMatrix_map]
    rfl
  exact congrFun (congrFun hM (coordinatePair j).2) (Fin.natAdd 2 (coordinatePair j).1)

def identityJacobian : Matrix (Fin 8) (Fin 8) K :=
  (!![0,0,0,0,0,0,0,2;
      0,0,0,-2,0,0,0,2;
      -2,0,0,0,0,0,0,0;
      0,0,-2,0,0,0,0,0;
      0,-2,0,0,0,2,0,0;
      0,0,0,0,0,2,0,0;
      0,0,0,0,0,0,2,0;
      0,0,0,0,-2,0,2,0] : Matrix (Fin 8) (Fin 8) K).transpose

/-- Every Jacobian entry is checked from the literal polynomial quotient formula. -/
theorem jacobian_atIdentity :
    (jacobianNumerator K).map (atIdentity K) = identityJacobian K := by
  ext i j
  change atIdentity K (denominator K * pderiv i (numerator K j) -
    numerator K j * pderiv i (denominator K)) = identityJacobian K i j
  rw [map_sub,map_mul,map_mul]
  change (atIdentityDual K i (denominator K)).fst * (atIdentityDual K i (numerator K j)).snd -
    (atIdentityDual K i (numerator K j)).fst * (atIdentityDual K i (denominator K)).snd = _
  rw [denominator_dual,numerator_dual]
  fin_cases i <;> fin_cases j <;>
    norm_num [dualPivot,dualFrame,atIdentityDual,
      quotientMatrix,congruence,symCoordinates,symMatrix,normalizedFrame,
      Matrix.adjugate_fin_three,Matrix.adjugate_fin_two,standardQuotient,Matrix.det_fin_two,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,Pi.single_apply,atIdentity,identityCoefficients,
      identityJacobian,smul_eq_mul,coordinatePair,finProdFinEquiv,Fin.divNat,Fin.modNat,Fin.natAdd]

variable [CharZero K]

def identityJacobianInverse : Matrix (Fin 8) (Fin 8) K :=
  (!![0,0,-1/2,0,0,0,0,0;
      0,0,0,0,-1/2,1/2,0,0;
      0,0,0,-1/2,0,0,0,0;
      1/2,-1/2,0,0,0,0,0,0;
      0,0,0,0,0,0,1/2,-1/2;
      0,0,0,0,0,1/2,0,0;
      0,0,0,0,0,0,1/2,0;
      1/2,0,0,0,0,0,0,0] : Matrix (Fin 8) (Fin 8) K).transpose

theorem identityJacobian_inverse : identityJacobianInverse K * identityJacobian K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [identityJacobian,identityJacobianInverse,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

theorem jacobianNumerator_det_ne_zero : (jacobianNumerator K).det ≠ 0 := by
  intro h
  have he : ((jacobianNumerator K).map (atIdentity K)).det = 0 := by
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det,h,map_zero]
  rw [jacobian_atIdentity] at he
  exact (Matrix.isUnit_det_of_left_inverse (identityJacobian_inverse K)).ne_zero he

abbrev rationalField := FractionRing (polynomial K)

def coordinate (j : Fin 8) : rationalField K :=
  algebraMap (polynomial K) (rationalField K) (numerator K j) /
    algebraMap (polynomial K) (rationalField K) (denominator K)

def coordinateDerivation (i : Fin 8) : Derivation K (rationalField K) (rationalField K) :=
  FractionDerivation.extend (pderiv i)

omit [CharZero K] in
theorem coordinate_derivative (i j : Fin 8) :
    coordinateDerivation K i (coordinate K j) =
      (algebraMap (polynomial K) (rationalField K) (denominator K))⁻¹ ^ 2 *
        algebraMap (polynomial K) (rationalField K) (jacobianNumerator K i j) := by
  rw [coordinate,Derivation.leibniz_div]
  simp only [coordinateDerivation,FractionDerivation.extend_algebraMap,smul_eq_mul,
    jacobianNumerator,map_sub,map_mul]

theorem coordinate_algebraicIndependent : AlgebraicIndependent K (coordinate K) := by
  apply JacobianIndependence.algebraicIndependent_of_derivations (coordinateDerivation K)
  have hd : algebraMap (polynomial K) (rationalField K) (denominator K) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (polynomial K) (rationalField K)).ne (denominator_ne_zero K)
  have hM : Matrix.of (fun i j => coordinateDerivation K i (coordinate K j)) =
      ((algebraMap (polynomial K) (rationalField K) (denominator K))⁻¹ ^ 2) •
        (jacobianNumerator K).map (algebraMap (polynomial K) (rationalField K)) := by
    ext i j
    exact coordinate_derivative K i j
  rw [hM,Matrix.det_smul,← RingHom.mapMatrix_apply,← RingHom.map_det]
  refine mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero hd))) ?_
  simpa only [map_zero] using
    (IsFractionRing.injective (polynomial K) (rationalField K)).ne
      (jacobianNumerator_det_ne_zero K)

end M9Native.ConicFrameCoordinates

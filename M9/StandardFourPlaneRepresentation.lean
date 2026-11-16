module

public import M9.ConicPencilFrames
public import M9.PrimitiveRepresentation
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Evaluation coordinates on the actual standard four-plane

Evaluation on the four literal diagonal vectors identifies the equal-diagonal
symmetric matrices with the permutation representation on four coordinates.
The action on matrices is actual congruence, so evaluation uses the inverse
permutation. Its determinant character is the sign character.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace M9.StandardFourPlaneRepresentation

open ConicPencilFrames TetrahedralGroup
open scoped BigOperators TensorProduct

abbrev S0 := ConicPencilFrames.standardFourPlane
abbrev Four := Fin 4 → ℂ

local instance s0AddCommGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

/-- Evaluation of an actual member of the displayed four-plane. -/
def evaluation (Q : S0) : Four :=
  fun i => quadraticValue Q.val (diagonal i)

theorem diagonal_entry_eq (Q : S0) (i : Fin 3) :
    Q.val.val i i = Q.val.val 0 0 := by
  fin_cases i
  · rfl
  · exact Q.property.1.symm
  · exact Q.property.2.symm.trans Q.property.1.symm

/-- The evaluation matrix is a Hadamard matrix times diag(3,2,2,2). -/
theorem evaluation_coordinates (Q : S0) :
    evaluation Q =
      ![3 * Q.val.val 0 0 + 2 * Q.val.val 0 1 + 2 * Q.val.val 0 2 + 2 * Q.val.val 1 2,
        3 * Q.val.val 0 0 - 2 * Q.val.val 0 1 - 2 * Q.val.val 0 2 + 2 * Q.val.val 1 2,
        3 * Q.val.val 0 0 - 2 * Q.val.val 0 1 + 2 * Q.val.val 0 2 - 2 * Q.val.val 1 2,
        3 * Q.val.val 0 0 + 2 * Q.val.val 0 1 - 2 * Q.val.val 0 2 - 2 * Q.val.val 1 2] := by
  have h11 := diagonal_entry_eq Q 1
  have h22 := diagonal_entry_eq Q 2
  funext i
  fin_cases i <;>
    norm_num [evaluation, quadraticValue_coordinates, diagonal, diagonalQ, h11, h22] <;> ring

/-- The inverse evaluation coefficients in the literal four-plane coordinates. -/
def recoverCoordinates (v : Four) : Four :=
  ![(v 0 + v 1 + v 2 + v 3) / 12,
    (v 0 - v 1 - v 2 + v 3) / 8,
    (v 0 - v 1 + v 2 - v 3) / 8,
    (v 0 + v 1 - v 2 - v 3) / 8]

/-- An actual linear equivalence, whose forward map is quadratic evaluation. -/
def evaluationEquiv : S0 ≃ₗ[ℂ] Four where
  toFun := evaluation
  invFun v := standardFourPlaneCoordinates.symm (recoverCoordinates v)
  left_inv Q := by
    apply standardFourPlaneCoordinates.injective
    change recoverCoordinates (evaluation Q) = standardFourPlaneCoordinates Q
    rw [evaluation_coordinates]
    funext i
    fin_cases i <;> simp [recoverCoordinates, standardFourPlaneCoordinates] <;> ring
  right_inv v := by
    rw [evaluation_coordinates]
    funext i
    fin_cases i <;> simp [recoverCoordinates, standardFourPlaneCoordinates] <;> ring
  map_add' Q R := by
    funext i
    exact quadraticValue_add Q.val R.val (diagonal i)
  map_smul' c Q := by
    funext i
    exact quadraticValue_smul_conic c Q.val (diagonal i)

@[simp] theorem evaluationEquiv_apply (Q : S0) (i : Fin 4) :
    evaluationEquiv Q i = quadraticValue Q.val (diagonal i) := rfl

theorem signed_congruence_diagonal (σ : Equiv.Perm (Fin 3))
    (ε : Fin 3 → Bool) (Q : Conic) (i : Fin 3) :
    (PrimitiveRepresentation.congruence ℂ (signedMatrix ℂ σ ε) Q).val i i =
      Q.val (σ i) (σ i) := by
  cases hi : ε i <;>
    simp [PrimitiveRepresentation.congruence_val, Matrix.mul_apply,
      Matrix.transpose_apply, signedMatrix, hi, ite_mul, mul_ite]

theorem congruence_mem (g : Gamma) (Q : S0) :
    PrimitiveRepresentation.congruence ℂ (matrix g) Q.val ∈ standardFourPlane := by
  obtain ⟨σ, ε, hg⟩ := matrix_isSignedPermutation g
  change _ = _ ∧ _ = _
  rw [hg]
  simp only [signed_congruence_diagonal]
  constructor <;>
    exact (diagonal_entry_eq Q _).trans (diagonal_entry_eq Q _).symm

/-- Actual congruence restricted to the actual equal-diagonal four-plane. -/
def gammaAction (g : Gamma) : S0 →ₗ[ℂ] S0 where
  toFun Q := ⟨PrimitiveRepresentation.congruence ℂ (matrix g) Q.val, congruence_mem g Q⟩
  map_add' Q R :=
    Subtype.ext ((PrimitiveRepresentation.congruence ℂ (matrix g)).map_add Q.val R.val)
  map_smul' c Q :=
    Subtype.ext ((PrimitiveRepresentation.congruence ℂ (matrix g)).map_smul c Q.val)

@[simp] theorem gammaAction_val (g : Gamma) (Q : S0) :
    (gammaAction g Q).val = PrimitiveRepresentation.congruence ℂ (matrix g) Q.val := rfl

@[simp] theorem matrix_one : matrix (1 : Gamma) = 1 := rfl
@[simp] theorem matrix_mul (g h : Gamma) : matrix (g * h) = matrix g * matrix h := rfl

theorem matrix_inv_transpose (g : Gamma) : matrix g⁻¹ = (matrix g).transpose := by
  have hi : matrix g⁻¹ * matrix g = 1 := by rw [← matrix_mul, inv_mul_cancel, matrix_one]
  calc
    matrix g⁻¹ = matrix g⁻¹ * 1 := (Matrix.mul_one _).symm
    _ = matrix g⁻¹ * (matrix g * (matrix g).transpose) := by rw [matrix_orthogonal]
    _ = (matrix g⁻¹ * matrix g) * (matrix g).transpose := (Matrix.mul_assoc _ _ _).symm
    _ = (matrix g).transpose := by rw [hi, Matrix.one_mul]

@[simp] theorem gammaAction_one (Q : S0) : gammaAction 1 Q = Q := by
  apply Subtype.ext
  simp

@[simp] theorem gammaAction_mul (g h : Gamma) (Q : S0) :
    gammaAction (g * h) Q = gammaAction g (gammaAction h Q) := by
  apply Subtype.ext
  simp

/-- The genuine linear automorphism induced by each literal group matrix. -/
def gammaActionEquiv (g : Gamma) : S0 ≃ₗ[ℂ] S0 :=
  { gammaAction g with
    invFun := gammaAction g⁻¹
    left_inv := fun Q => by
      change gammaAction g⁻¹ (gammaAction g Q) = Q
      rw [← gammaAction_mul, inv_mul_cancel, gammaAction_one]
    right_inv := fun Q => by
      change gammaAction g (gammaAction g⁻¹ Q) = Q
      rw [← gammaAction_mul, mul_inv_cancel, gammaAction_one] }

/-- The actual representation, before choosing evaluation coordinates. -/
def gammaRepresentation : Gamma →* (S0 ≃ₗ[ℂ] S0) where
  toFun := gammaActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro Q
    exact gammaAction_one Q
  map_mul' g h := by
    apply LinearEquiv.ext
    intro Q
    exact gammaAction_mul g h Q

theorem quadraticValue_congruence (M : Mat3) (Q : Conic) (v : Vec3) :
    quadraticValue (PrimitiveRepresentation.congruence ℂ M Q) v =
      quadraticValue Q (M.transpose.mulVec v) := by
  simp only [quadraticValue, PrimitiveRepresentation.congruence_val, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.isValue, Fin.succ_zero_eq_one, Fin.reduceSucc, add_zero]
  ring

theorem orientation_sq (π : S4) : orientation π ^ 2 = 1 := by
  rcases orientationQ_sign π with h | h <;> norm_num [orientation, h]

/-- Congruence acts by the inverse permutation on the four evaluation coordinates. -/
theorem evaluation_gammaAction (g : Gamma) (Q : S0) (i : Fin 4) :
    evaluation (gammaAction g Q) i = evaluation Q ((framePermutation g)⁻¹ i) := by
  change quadraticValue (PrimitiveRepresentation.congruence ℂ (matrix g) Q.val) (diagonal i) = _
  rw [quadraticValue_congruence, ← matrix_inv_transpose, matrix_diagonal,
    quadraticValue_smul, orientation_sq, one_mul]
  simp only [map_inv]
  rfl

/-- The usual left permutation representation on functions on four points. -/
def permutationEquiv (π : S4) : Four ≃ₗ[ℂ] Four :=
  LinearEquiv.funCongrLeft ℂ ℂ π.symm

@[simp] theorem permutationEquiv_apply (π : S4) (v : Four) (i : Fin 4) :
    permutationEquiv π v i = v (π⁻¹ i) := rfl

theorem evaluationEquiv_equivariant (g : Gamma) (Q : S0) :
    evaluationEquiv (gammaActionEquiv g Q) =
      permutationEquiv (framePermutation g) (evaluationEquiv Q) := by
  funext i
  exact evaluation_gammaAction g Q i

theorem evaluation_conjugate (g : Gamma) :
    (evaluationEquiv.symm.trans (gammaActionEquiv g)).trans evaluationEquiv =
      permutationEquiv (framePermutation g) := by
  apply LinearEquiv.ext
  intro v
  change evaluationEquiv (gammaActionEquiv g (evaluationEquiv.symm v)) = _
  rw [evaluationEquiv_equivariant, LinearEquiv.apply_symm_apply]

/-- The sign character, mapped from integral units to actual complex units. -/
def signCharacter : S4 →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

@[simp] theorem signCharacter_val (π : S4) :
    (signCharacter π : ℂ) = ((Equiv.Perm.sign π : ℤ) : ℂ) := rfl

theorem signCharacter_inv (π : S4) : (signCharacter π)⁻¹ = signCharacter π := by
  rw [← map_inv]
  exact congrArg (Units.map (Int.castRingHom ℂ).toMonoidHom) (Equiv.Perm.sign_inv π)

theorem permutationEquiv_toMatrix (π : S4) :
    LinearMap.toMatrix' (permutationEquiv π).toLinearMap =
      (1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix π.symm id := by
  ext i j
  simp [LinearMap.toMatrix'_apply, permutationEquiv_apply, Matrix.one_apply,
    Pi.single_apply, eq_comm]

theorem permutationEquiv_det (π : S4) :
    LinearEquiv.det (permutationEquiv π) = signCharacter π := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', permutationEquiv_toMatrix,
    Matrix.det_permute]
  simp [Equiv.Perm.sign_symm]

/-- The determinant is that of the actual restricted matrix action. -/
theorem gammaAction_det (g : Gamma) :
    LinearEquiv.det (gammaActionEquiv g) = signCharacter (framePermutation g) := by
  calc
    _ = LinearEquiv.det
        ((evaluationEquiv.symm.trans (gammaActionEquiv g)).trans evaluationEquiv) :=
      (LinearEquiv.det_conj (gammaActionEquiv g) evaluationEquiv).symm
    _ = _ := by rw [evaluation_conjugate, permutationEquiv_det]

def determinantCharacter : Gamma →* ℂˣ := LinearEquiv.det.comp gammaRepresentation

theorem determinantCharacter_eq_sign (g : Gamma) :
    determinantCharacter g = signCharacter (framePermutation g) := gammaAction_det g

/-- The actual determinant-inverse twist of the matrix action. -/
def determinantTwistedEquiv (g : Gamma) : S0 ≃ₗ[ℂ] S0 :=
  (gammaActionEquiv g).trans
    (LinearEquiv.smulOfUnit ((LinearEquiv.det (gammaActionEquiv g))⁻¹))

@[simp] theorem determinantTwistedEquiv_apply (g : Gamma) (Q : S0) :
    determinantTwistedEquiv g Q =
      (↑((LinearEquiv.det (gammaActionEquiv g))⁻¹) : ℂ) • gammaActionEquiv g Q := rfl

/-- The signed permutation action on four actual coordinate values. -/
def signedPermutationEquiv (π : S4) : Four ≃ₗ[ℂ] Four :=
  (permutationEquiv π).trans (LinearEquiv.smulOfUnit (signCharacter π))

@[simp] theorem signedPermutationEquiv_apply (π : S4) (v : Four) (i : Fin 4) :
    signedPermutationEquiv π v i = (signCharacter π : ℂ) * v (π⁻¹ i) := rfl

/-- Evaluation identifies the actual determinant twist with signed permutation. -/
theorem evaluationEquiv_twisted (g : Gamma) (Q : S0) :
    evaluationEquiv (determinantTwistedEquiv g Q) =
      signedPermutationEquiv (framePermutation g) (evaluationEquiv Q) := by
  rw [determinantTwistedEquiv_apply, map_smul, evaluationEquiv_equivariant,
    gammaAction_det, signCharacter_inv]
  rfl

theorem signedPermutationEquiv_one (v : Four) : signedPermutationEquiv 1 v = v := by
  funext i
  simp

theorem signedPermutationEquiv_mul (π τ : S4) (v : Four) :
    signedPermutationEquiv (π * τ) v =
      signedPermutationEquiv π (signedPermutationEquiv τ v) := by
  funext i
  simp [mul_assoc]

def signedPermutationRepresentation : S4 →* (Four ≃ₗ[ℂ] Four) where
  toFun := signedPermutationEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact signedPermutationEquiv_one v
  map_mul' π τ := by
    apply LinearEquiv.ext
    intro v
    exact signedPermutationEquiv_mul π τ v

def gammaSignedPermutationRepresentation : Gamma →* (Four ≃ₗ[ℂ] Four) :=
  signedPermutationRepresentation.comp framePermutation.toMonoidHom

/-- The determinant-inverse twist is itself a genuine representation. -/
def determinantTwistedRepresentation : Gamma →* (S0 ≃ₗ[ℂ] S0) where
  toFun := determinantTwistedEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro Q
    apply evaluationEquiv.injective
    change evaluationEquiv (determinantTwistedEquiv 1 Q) = evaluationEquiv Q
    rw [evaluationEquiv_twisted, map_one, signedPermutationEquiv_one]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro Q
    apply evaluationEquiv.injective
    change evaluationEquiv (determinantTwistedEquiv (g * h) Q) =
      evaluationEquiv (determinantTwistedEquiv g (determinantTwistedEquiv h Q))
    simp only [evaluationEquiv_twisted, map_mul, signedPermutationEquiv_mul]

/-- Orthogonality identifies the second, contragredient symmetric-matrix action
with the same literal congruence action on the second standard four-plane. -/
theorem dual_congruence_eq (g : Gamma) (Q : Conic) :
    PrimitiveRepresentation.congruence ℂ (matrix g⁻¹).transpose Q =
      PrimitiveRepresentation.congruence ℂ (matrix g) Q := by
  rw [matrix_inv_transpose, Matrix.transpose_transpose]

theorem evaluation_dual_congruence (g : Gamma) (Q : S0) (i : Fin 4) :
    quadraticValue
        (PrimitiveRepresentation.congruence ℂ (matrix g⁻¹).transpose Q.val) (diagonal i) =
      evaluation Q ((framePermutation g)⁻¹ i) := by
  rw [dual_congruence_eq]
  exact evaluation_gammaAction g Q i

/-- A basis of actual matrices obtained from the four evaluation delta functions. -/
def evaluationBasis : Module.Basis (Fin 4) ℂ S0 :=
  (Pi.basisFun ℂ (Fin 4)).map evaluationEquiv.symm

/-- The genuine dual of the top exterior power, not an assumed character line. -/
abbrev DeterminantDual := Module.Dual ℂ (⋀[ℂ]^4 S0)

def alternatingDeterminantCoordinates :
    (S0 [⋀^Fin 4]→ₗ[ℂ] ℂ) ≃ₗ[ℂ] ℂ where
  toFun φ := φ evaluationBasis
  invFun c := c • evaluationBasis.det
  left_inv φ := (φ.eq_smul_basis_det evaluationBasis).symm
  right_inv c := by simp [Module.Basis.det_self]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation on the actual exterior volume identifies the determinant dual with ℂ. -/
def determinantDualCoordinates : DeterminantDual ≃ₗ[ℂ] ℂ :=
  (exteriorPower.alternatingMapLinearEquiv (R := ℂ) (n := 4)
    (M := S0) (N := ℂ)).symm.trans alternatingDeterminantCoordinates

@[simp] theorem determinantDualCoordinates_apply (φ : DeterminantDual) :
    determinantDualCoordinates φ = φ (exteriorPower.ιMulti ℂ 4 evaluationBasis) := by
  exact exteriorPower.alternatingMapLinearEquiv_symm_apply φ evaluationBasis

/-- The literal contragredient of the induced fourth exterior-power map. -/
def determinantDualAction (g : Gamma) : DeterminantDual →ₗ[ℂ] DeterminantDual :=
  (exteriorPower.map 4 (gammaActionEquiv g).symm.toLinearMap).dualMap

theorem determinantDualAction_coordinates (g : Gamma) (φ : DeterminantDual) :
    determinantDualCoordinates (determinantDualAction g φ) =
      (↑((LinearEquiv.det (gammaActionEquiv g))⁻¹) : ℂ) * determinantDualCoordinates φ := by
  let a : S0 [⋀^Fin 4]→ₗ[ℂ] ℂ := exteriorPower.alternatingMapLinearEquiv.symm φ
  have ha := congrArg (fun z : S0 [⋀^Fin 4]→ₗ[ℂ] ℂ =>
      z ((gammaActionEquiv g).symm.toLinearMap ∘ evaluationBasis))
    (a.eq_smul_basis_det evaluationBasis)
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one, ← LinearEquiv.coe_inv_det] at ha
  rw [determinantDualCoordinates_apply, determinantDualCoordinates_apply]
  change φ ((exteriorPower.map 4 (gammaActionEquiv g).symm.toLinearMap)
    (exteriorPower.ιMulti ℂ 4 evaluationBasis)) = _
  rw [exteriorPower.map_apply_ιMulti]
  change a ((gammaActionEquiv g).symm.toLinearMap ∘ evaluationBasis) =
    (↑((LinearEquiv.det (gammaActionEquiv g))⁻¹) : ℂ) * a evaluationBasis
  simpa only [mul_comm] using ha

/-- The actual determinant-twisted four-dimensional module. -/
abbrev E0 := S0 ⊗[ℂ] DeterminantDual

/-- Evaluation coordinates on the literal tensor product S0 ⊗ det(S0)∨. -/
def tensorEvaluationEquiv : E0 ≃ₗ[ℂ] Four :=
  (TensorProduct.congr evaluationEquiv determinantDualCoordinates).trans
    (TensorProduct.rid ℂ Four)

@[simp] theorem tensorEvaluationEquiv_tmul (Q : S0) (φ : DeterminantDual) :
    tensorEvaluationEquiv (Q ⊗ₜ[ℂ] φ) = determinantDualCoordinates φ • evaluationEquiv Q := rfl

/-- The actual tensor of matrix congruence and dual exterior action. -/
def tensorAction (g : Gamma) : E0 →ₗ[ℂ] E0 :=
  TensorProduct.map (gammaAction g) (determinantDualAction g)

theorem tensorEvaluationEquiv_equivariant (g : Gamma) (x : E0) :
    tensorEvaluationEquiv (tensorAction g x) =
      signedPermutationEquiv (framePermutation g) (tensorEvaluationEquiv x) := by
  induction x using TensorProduct.inductionOn with
  | tmul Q φ =>
      change tensorEvaluationEquiv
          (gammaActionEquiv g Q ⊗ₜ[ℂ] determinantDualAction g φ) = _
      rw [tensorEvaluationEquiv_tmul, tensorEvaluationEquiv_tmul,
        determinantDualAction_coordinates, gammaAction_det, signCharacter_inv,
        evaluationEquiv_equivariant]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, signedPermutationEquiv_apply,
        permutationEquiv_apply]
      ring
  | add x y hx hy =>
      calc
        _ = tensorEvaluationEquiv (tensorAction g x) +
            tensorEvaluationEquiv (tensorAction g y) := by
          rw [(tensorAction g).map_add, tensorEvaluationEquiv.map_add]
        _ = signedPermutationEquiv (framePermutation g) (tensorEvaluationEquiv x) +
            signedPermutationEquiv (framePermutation g) (tensorEvaluationEquiv y) :=
          congrArg₂ (· + ·) hx hy
        _ = _ := by
          rw [tensorEvaluationEquiv.map_add,
            (signedPermutationEquiv (framePermutation g)).map_add]

theorem tensorAction_one (x : E0) : tensorAction 1 x = x := by
  apply tensorEvaluationEquiv.injective
  rw [tensorEvaluationEquiv_equivariant, map_one, signedPermutationEquiv_one]

theorem tensorAction_mul (g h : Gamma) (x : E0) :
    tensorAction (g * h) x = tensorAction g (tensorAction h x) := by
  apply tensorEvaluationEquiv.injective
  simp only [tensorEvaluationEquiv_equivariant, map_mul, signedPermutationEquiv_mul]

def tensorActionEquiv (g : Gamma) : E0 ≃ₗ[ℂ] E0 :=
  { tensorAction g with
    invFun := tensorAction g⁻¹
    left_inv := fun x => by
      change tensorAction g⁻¹ (tensorAction g x) = x
      rw [← tensorAction_mul, inv_mul_cancel, tensorAction_one]
    right_inv := fun x => by
      change tensorAction g (tensorAction g⁻¹ x) = x
      rw [← tensorAction_mul, mul_inv_cancel, tensorAction_one] }

/-- A genuine representation on the literal determinant-twisted module. -/
def tensorRepresentation : Gamma →* (E0 ≃ₗ[ℂ] E0) where
  toFun := tensorActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact tensorAction_one x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact tensorAction_mul g h x

def tensorBasis : Module.Basis (Fin 4) ℂ E0 :=
  (Pi.basisFun ℂ (Fin 4)).map tensorEvaluationEquiv.symm

@[simp] theorem tensorBasis_evaluation (j i : Fin 4) :
    tensorEvaluationEquiv (tensorBasis j) i = if i = j then 1 else 0 := by
  simp [tensorBasis, Pi.basisFun_apply, Pi.single_apply]

theorem finrank_E0 : Module.finrank ℂ E0 = 4 := by
  rw [tensorEvaluationEquiv.finrank_eq]
  simp

theorem tensorAction_coordinates (g : Gamma) (x : E0) (i : Fin 4) :
    tensorEvaluationEquiv (tensorActionEquiv g x) i =
      (signCharacter (framePermutation g) : ℂ) *
        tensorEvaluationEquiv x ((framePermutation g)⁻¹ i) := by
  exact congrFun (tensorEvaluationEquiv_equivariant g x) i

end M9.StandardFourPlaneRepresentation

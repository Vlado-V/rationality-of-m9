module

public import M9StacksIntegration.LagrangianTransitivity

/-!
# The primitive exterior representation over coordinate rings

The primitive module is the kernel of contraction on the actual third
exterior power over an arbitrary commutative ring. The checked constant
matrix decomposition of the field model supplies its fourteen coordinates
after every coefficient-ring homomorphism, including nonreduced rings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module Matrix exteriorPower

universe u

namespace M9Native.PrimitiveRingRepresentation

open LagrangianRing LagrangianTransitivity

variable (R : Type u) [CommRing R]

/-- The genuine primitive kernel over the coefficient ring. -/
def Primitive : Submodule R (Third R) := LinearMap.ker (contraction R)

theorem contractionMatrix_coordinates (w : Third R) :
    contractionMatrix R *ᵥ (thirdBasis20 R).equivFun w = contraction R w := by
  change LinearMap.toMatrix (thirdBasis20 R) (Pi.basisFun R (Fin 6)) (contraction R) *ᵥ
    (thirdBasis20 R).repr w = contraction R w
  rw [LinearMap.toMatrix_mulVec_repr]
  rfl

section Coordinates

variable (K : Type u) [Field K] [CharZero K] (f : K →+* R)

/-- Inclusion of the fourteen coordinates into the actual exterior power. -/
def embedding : (Fin 14 → R) →ₗ[R] Third R :=
  (thirdBasis20 R).equivFun.symm.toLinearMap.comp
    ((LagrangianField.embeddingMatrix K).map f).mulVecLin

/-- The original constant retraction extended to the coefficient ring. -/
def projection : Third R →ₗ[R] (Fin 14 → R) :=
  ((LagrangianField.projectionMatrix K).map f).mulVecLin.comp
    (thirdBasis20 R).equivFun.toLinearMap

theorem contractionMatrix_embeddingMatrix :
    contractionMatrix R * (LagrangianField.embeddingMatrix K).map f = 0 := by
  rw [← contractionMatrix_map R f, ← Matrix.map_mul]
  have h : LagrangianField.contractionMatrix K * LagrangianField.embeddingMatrix K = 0 := by
    rw [LagrangianField.contractionMatrix, LagrangianField.embeddingMatrix,
      ← LinearMap.toMatrix_comp]
    have hc : (LagrangianField.contraction K).comp (LagrangianField.coordinateEmbedding K) = 0 := by
      apply LinearMap.ext
      intro v
      exact LagrangianField.contraction_embedding K v
    rw [hc, map_zero]
  rw [h]
  exact Matrix.map_zero _ (map_zero f)

omit [CharZero K] in
theorem embedding_coordinates (v : Fin 14 → R) :
    (thirdBasis20 R).equivFun (embedding R K f v) =
      (LagrangianField.embeddingMatrix K).map f *ᵥ v := by
  simp only [embedding, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply]

omit [CharZero K] in
theorem projection_apply (w : Third R) :
    projection R K f w = (LagrangianField.projectionMatrix K).map f *ᵥ
      (thirdBasis20 R).equivFun w := rfl

theorem contraction_embedding (v : Fin 14 → R) :
    contraction R (embedding R K f v) = 0 := by
  rw [← contractionMatrix_coordinates]
  rw [embedding_coordinates]
  rw [Matrix.mulVec_mulVec, contractionMatrix_embeddingMatrix, Matrix.zero_mulVec]

omit [CharZero K] in
theorem projection_embedding (v : Fin 14 → R) :
    projection R K f (embedding R K f v) = v := by
  rw [projection_apply, embedding_coordinates]
  rw [Matrix.mulVec_mulVec, LagrangianField.primitive_matrix_leftInverse_map,
    Matrix.one_mulVec]

theorem embedding_projection (w : Third R) (hw : contraction R w = 0) :
    embedding R K f (projection R K f w) = w := by
  apply (thirdBasis20 R).equivFun.injective
  rw [embedding_coordinates, projection_apply]
  apply LagrangianField.primitive_vector_reconstruction K f
  rw [contractionMatrix_map, contractionMatrix_coordinates, hw]

/-- The proved coordinate equivalence of the actual primitive kernel over every ring. -/
def coordinates : Primitive R ≃ₗ[R] (Fin 14 → R) where
  toFun w := projection R K f w.val
  invFun v := ⟨embedding R K f v, contraction_embedding R K f v⟩
  left_inv w := Subtype.ext (embedding_projection R K f w.val w.property)
  right_inv v := projection_embedding R K f v
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

@[simp] theorem coordinates_apply (w : Primitive R) :
    coordinates R K f w = projection R K f w.val := rfl

@[simp] theorem coordinates_symm_val (v : Fin 14 → R) :
    ((coordinates R K f).symm v).val = embedding R K f v := rfl

end Coordinates

theorem matrixSix_one : matrixSix R (1 : Matrix.symplecticGroup (Fin 3) R) = 1 := by
  change (1 : Matrix SplitIndex SplitIndex R).submatrix splitIndex.symm splitIndex.symm = 1
  exact Matrix.submatrix_one_equiv splitIndex.symm

theorem matrixSix_mul (g h : Matrix.symplecticGroup (Fin 3) R) :
    matrixSix R (g * h) = matrixSix R g * matrixSix R h := by
  change ((g : Matrix SplitIndex SplitIndex R) * (h : Matrix SplitIndex SplitIndex R)).submatrix
    splitIndex.symm splitIndex.symm = _
  exact (Matrix.submatrix_mul_equiv _ _ splitIndex.symm splitIndex.symm splitIndex.symm).symm

/-- The actual third exterior map of a ring-valued symplectic matrix. -/
def exteriorAction (g : Matrix.symplecticGroup (Fin 3) R) : Third R →ₗ[R] Third R :=
  exteriorPower.map 3 (matrixSix R g).mulVecLin

theorem exteriorAction_one : exteriorAction R 1 = LinearMap.id := by
  rw [exteriorAction, matrixSix_one]
  have h : (1 : Matrix (Fin 6) (Fin 6) R).mulVecLin = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact Matrix.one_mulVec v
  rw [h, exteriorPower.map_id]

theorem exteriorAction_mul (g h : Matrix.symplecticGroup (Fin 3) R) :
    exteriorAction R (g * h) = (exteriorAction R g).comp (exteriorAction R h) := by
  rw [exteriorAction, matrixSix_mul]
  have hm : (matrixSix R g * matrixSix R h).mulVecLin =
      (matrixSix R g).mulVecLin.comp (matrixSix R h).mulVecLin := by
    apply LinearMap.ext
    intro v
    exact (Matrix.mulVec_mulVec v (matrixSix R g) (matrixSix R h)).symm
  rw [hm, exteriorPower.map_comp]
  rfl

/-- Symplectic contraction is natural over arbitrary commutative rings. -/
theorem contraction_natural (g : Matrix.symplecticGroup (Fin 3) R) :
    (contraction R).comp (exteriorAction R g) =
      (matrixSix R g).mulVecLin.comp (contraction R) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change contraction R (exteriorAction R g (exteriorPower.ιMulti R 3 v)) =
    (matrixSix R g).mulVecLin (contraction R (exteriorPower.ιMulti R 3 v))
  simp only [exteriorAction, exteriorPower.map_apply_ιMulti, contraction_ιMulti,
    contractionFormula, tripleContract, Function.comp_apply,
    LinearMap.map_add, LinearMap.map_sub, LinearMap.map_smul]
  simp only [Matrix.mulVecLin_apply, matrixSix_preserves_omega]

/-- The actual primitive kernel is preserved on every coefficient ring. -/
def primitiveAction (g : Matrix.symplecticGroup (Fin 3) R) : Primitive R →ₗ[R] Primitive R :=
  ((exteriorAction R g).comp (Primitive R).subtype).codRestrict (Primitive R) (by
    intro w
    change contraction R (exteriorAction R g w.val) = 0
    have h := LinearMap.congr_fun (contraction_natural R g) w.val
    change contraction R (exteriorAction R g w.val) = (matrixSix R g).mulVecLin _ at h
    rw [w.property, map_zero] at h
    exact h)

@[simp] theorem primitiveAction_val (g : Matrix.symplecticGroup (Fin 3) R) (w : Primitive R) :
    (primitiveAction R g w).val = exteriorAction R g w.val := rfl

theorem primitiveAction_one : primitiveAction R 1 = LinearMap.id := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact LinearMap.congr_fun (exteriorAction_one R) w.val

theorem primitiveAction_mul (g h : Matrix.symplecticGroup (Fin 3) R) :
    primitiveAction R (g * h) = (primitiveAction R g).comp (primitiveAction R h) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact LinearMap.congr_fun (exteriorAction_mul R g h) w.val

/-- The inverse symplectic matrix supplies the genuine inverse primitive map. -/
def primitiveLinear (g : Matrix.symplecticGroup (Fin 3) R) : Primitive R ≃ₗ[R] Primitive R :=
  LinearEquiv.ofLinearMap (primitiveAction R g) (primitiveAction R g⁻¹)
    (by rw [← primitiveAction_mul, mul_inv_cancel, primitiveAction_one])
    (by rw [← primitiveAction_mul, inv_mul_cancel, primitiveAction_one])

def primitiveRepresentation : Matrix.symplecticGroup (Fin 3) R →* (Primitive R ≃ₗ[R] Primitive R) where
  toFun := primitiveLinear R
  map_one' := LinearEquiv.toLinearMap_injective (primitiveAction_one R)
  map_mul' g h := LinearEquiv.toLinearMap_injective (primitiveAction_mul R g h)

end M9Native.PrimitiveRingRepresentation

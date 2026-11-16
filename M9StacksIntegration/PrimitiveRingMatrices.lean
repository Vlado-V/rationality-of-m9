module

public import M9StacksIntegration.PrimitiveRingRepresentation

/-! The coefficient-ring-natural matrices of the actual primitive exterior representation. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix Module exteriorPower

universe u

namespace M9Native.PrimitiveRingMatrices

open LagrangianRing LagrangianTransitivity PrimitiveRingRepresentation

variable (R : Type u) [CommRing R]

def exteriorMatrix (g : Matrix.symplecticGroup (Fin 3) R) : Matrix (Fin 20) (Fin 20) R :=
  LinearMap.toMatrix (thirdBasis20 R) (thirdBasis20 R) (exteriorAction R g)

theorem exteriorMatrix_coordinates (g : Matrix.symplecticGroup (Fin 3) R) (w : Third R) :
    exteriorMatrix R g *ᵥ (thirdBasis20 R).equivFun w =
      (thirdBasis20 R).equivFun (exteriorAction R g w) :=
  LinearMap.toMatrix_mulVec_repr _ _ _ _

/-- The actual third exterior representation has the literal three-by-three minors. -/
theorem exteriorMatrix_apply (g : Matrix.symplecticGroup (Fin 3) R) (i j : Fin 20) :
    exteriorMatrix R g i j =
      Matrix.det ((matrixSix R g).submatrix (triple i) (triple j)) := by
  let M : Matrix (Fin 3) (Fin 6) R := fun a b => matrixSix R g b (triple j a)
  have ha : exteriorAction R g (thirdBasis20 R j) = rowPlucker R M := by
    rw [thirdBasis20_apply, exteriorAction, exteriorPower.map_apply_ιMulti]
    apply congrArg (exteriorPower.ιMulti R 3)
    funext a b
    simp [M, basisVector]
  rw [exteriorMatrix, LinearMap.toMatrix_apply, ha]
  change rowTwenty R M i = _
  rw [rowTwenty_eq_minor]
  have hm : M.submatrix id (triple i) =
      ((matrixSix R g).submatrix (triple i) (triple j)).transpose := rfl
  rw [hm, Matrix.det_transpose]

theorem exteriorMatrix_map {S : Type u} [CommRing S] (ρ : R →+* S)
    (g : Matrix.symplecticGroup (Fin 3) R) :
    exteriorMatrix S (mapSymplectic R ρ g) = (exteriorMatrix R g).map ρ := by
  ext i j
  rw [exteriorMatrix_apply, Matrix.map_apply, exteriorMatrix_apply,
    matrixSix_map, RingHom.map_det]
  rfl

section PrimitiveMatrices

variable (K : Type u) [Field K] [CharZero K] (f : K →+* R)

/-- Literal polynomial exterior coefficients followed by the proved primitive projection. -/
def matrix14 (g : Matrix.symplecticGroup (Fin 3) R) : Matrix (Fin 14) (Fin 14) R :=
  (LagrangianField.projectionMatrix K).map f * exteriorMatrix R g *
    (LagrangianField.embeddingMatrix K).map f

def coordinateLinear (g : Matrix.symplecticGroup (Fin 3) R) :
    (Fin 14 → R) ≃ₗ[R] (Fin 14 → R) :=
  (coordinates R K f).symm.trans ((primitiveLinear R g).trans (coordinates R K f))

theorem matrix14_mulVec (g : Matrix.symplecticGroup (Fin 3) R) (v : Fin 14 → R) :
    matrix14 R K f g *ᵥ v = coordinateLinear R K f g v := by
  rw [matrix14, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [← embedding_coordinates R K f v, exteriorMatrix_coordinates]
  rfl

theorem matrix14_eq_toMatrix (g : Matrix.symplecticGroup (Fin 3) R) :
    matrix14 R K f g = LinearMap.toMatrix' (coordinateLinear R K f g).toLinearMap := by
  have h : Matrix.toLin' (matrix14 R K f g) = (coordinateLinear R K f g).toLinearMap := by
    apply LinearMap.ext
    exact matrix14_mulVec R K f g
  have h' := congrArg LinearMap.toMatrix' h
  simpa only [LinearMap.toMatrix'_toLin'] using h'

theorem coordinateLinear_one : coordinateLinear R K f 1 = LinearEquiv.refl R _ := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  change coordinates R K f (primitiveAction R 1 ((coordinates R K f).symm v)) = v
  rw [primitiveAction_one]
  exact (coordinates R K f).apply_symm_apply v

theorem coordinateLinear_mul (g h : Matrix.symplecticGroup (Fin 3) R) :
    coordinateLinear R K f (g * h) = coordinateLinear R K f g * coordinateLinear R K f h := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  change coordinates R K f (primitiveAction R (g*h) ((coordinates R K f).symm v)) =
    coordinates R K f (primitiveAction R g ((coordinates R K f).symm
      (coordinates R K f (primitiveAction R h ((coordinates R K f).symm v)))))
  rw [LinearEquiv.symm_apply_apply, primitiveAction_mul]
  rfl

theorem matrix14_one : matrix14 R K f 1 = 1 := by
  rw [matrix14_eq_toMatrix, coordinateLinear_one]
  exact LinearMap.toMatrix'_id

theorem matrix14_mul (g h : Matrix.symplecticGroup (Fin 3) R) :
    matrix14 R K f (g*h) = matrix14 R K f g * matrix14 R K f h := by
  rw [matrix14_eq_toMatrix, matrix14_eq_toMatrix, matrix14_eq_toMatrix, coordinateLinear_mul]
  exact LinearMap.toMatrix'_comp _ _

theorem matrix14_isUnit (g : Matrix.symplecticGroup (Fin 3) R) :
    IsUnit (matrix14 R K f g) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_exists_inv.mpr
  refine ⟨(matrix14 R K f g⁻¹).det, ?_⟩
  rw [← Matrix.det_mul, ← matrix14_mul, mul_inv_cancel, matrix14_one, Matrix.det_one]

omit [CharZero K] in
/-- Every change of coefficient ring carries the literal primitive matrix to its image. -/
theorem matrix14_map {S : Type u} [CommRing S] (ρ : R →+* S)
    (g : Matrix.symplecticGroup (Fin 3) R) :
    matrix14 S K (ρ.comp f) (mapSymplectic R ρ g) = (matrix14 R K f g).map ρ := by
  simp only [matrix14, exteriorMatrix_map, Matrix.map_mul, Matrix.map_map]
  rfl

end PrimitiveMatrices

end M9Native.PrimitiveRingMatrices

module

public import M9StacksIntegration.PrimitiveRingCoordinates

/-! The coefficient-ring representation specializes to the original symplectic action. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix Module exteriorPower

namespace M9Native.PrimitiveRingFieldBridge

open LagrangianTransitivity PrimitiveRingCoordinates

/-- A genuine matrix symplectic transformation is the original symplectic linear equivalence. -/
def toOriginal : Matrix.symplecticGroup (Fin 3) ℂ →* M9.PrimitiveStabilizer.Sp6 ℂ where
  toFun g := ⟨symplecticEquiv ℂ g, by
    intro v w
    exact symplecticEquiv_preserves_omega ℂ g v w⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change matrixSix ℂ 1 *ᵥ v = v
    rw [PrimitiveRingRepresentation.matrixSix_one, Matrix.one_mulVec]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change matrixSix ℂ (g*h) *ᵥ v = matrixSix ℂ g *ᵥ (matrixSix ℂ h *ᵥ v)
    rw [PrimitiveRingRepresentation.matrixSix_mul, Matrix.mulVec_mulVec]

theorem toOriginal_apply (g : Matrix.symplecticGroup (Fin 3) ℂ) (v : Fin 6 → ℂ) :
    (toOriginal g).val v = matrixSix ℂ g *ᵥ v := rfl

theorem splitBasis_repr (v : Fin 6 → ℂ) (i : Fin 3 ⊕ Fin 3) :
    (M9.PrimitiveStabilizer.splitBasis ℂ).repr v i = v (splitIndex i) := by
  cases i <;> rfl

theorem splitBasis_vector (i : Fin 3 ⊕ Fin 3) :
    M9.PrimitiveStabilizer.splitBasis ℂ i = Pi.single (splitIndex i) 1 := by
  cases i with
  | inl i => exact M9.PrimitiveStabilizer.splitBasis_inl ℂ i
  | inr i => exact M9.PrimitiveStabilizer.splitBasis_inr ℂ i

def fromOriginal : M9.PrimitiveStabilizer.Sp6 ℂ →* Matrix.symplecticGroup (Fin 3) ℂ where
  toFun h := ⟨LinearMap.toMatrix (M9.PrimitiveStabilizer.splitBasis ℂ)
    (M9.PrimitiveStabilizer.splitBasis ℂ) h.val.toLinearMap,
    M9.PrimitiveStabilizer.symplectic_matrix ℂ h⟩
  map_one' := by
    apply Subtype.ext
    exact LinearMap.toMatrix_id _
  map_mul' g h := by
    apply Subtype.ext
    exact LinearMap.toMatrix_comp _ _ _ _ _

theorem matrixSix_fromOriginal (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    matrixSix ℂ (fromOriginal h) = LinearMap.toMatrix' h.val.toLinearMap := by
  ext i j
  change LinearMap.toMatrix (M9.PrimitiveStabilizer.splitBasis ℂ)
    (M9.PrimitiveStabilizer.splitBasis ℂ) h.val.toLinearMap
      (splitIndex.symm i) (splitIndex.symm j) = _
  rw [LinearMap.toMatrix_apply, splitBasis_repr, splitBasis_vector,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, LinearMap.toMatrix'_apply]

theorem toOriginal_fromOriginal (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    toOriginal (fromOriginal h) = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  change matrixSix ℂ (fromOriginal h) *ᵥ v = h.val v
  rw [matrixSix_fromOriginal, LinearMap.toMatrix'_mulVec]
  rfl

theorem fromOriginal_toOriginal (g : Matrix.symplecticGroup (Fin 3) ℂ) :
    fromOriginal (toOriginal g) = g := by
  apply Subtype.ext
  ext i j
  change LinearMap.toMatrix (M9.PrimitiveStabilizer.splitBasis ℂ)
    (M9.PrimitiveStabilizer.splitBasis ℂ) (toOriginal g).val.toLinearMap i j = g.val i j
  rw [LinearMap.toMatrix_apply, splitBasis_repr, splitBasis_vector]
  change (matrixSix ℂ g *ᵥ Pi.single (splitIndex j) 1) (splitIndex i) = g.val i j
  rw [Matrix.mulVec_single_one]
  change matrixSix ℂ g (splitIndex i) (splitIndex j) = g.val i j
  simp only [matrixSix, Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- The matrix-valued points are exactly the frozen original symplectic group. -/
def originalGroupEquiv : Matrix.symplecticGroup (Fin 3) ℂ ≃* M9.PrimitiveStabilizer.Sp6 ℂ where
  toFun := toOriginal
  invFun := fromOriginal
  left_inv := fromOriginal_toOriginal
  right_inv := toOriginal_fromOriginal
  map_mul' := toOriginal.map_mul

/-- The primitive-kernel action is the literal original exterior action under the kernel
identification, not a second abstract representation of the same dimension. -/
theorem originalKernelEquiv_primitiveLinear (g : Matrix.symplecticGroup (Fin 3) ℂ)
    (w : PrimitiveRingRepresentation.Primitive ℂ) :
    originalKernelEquiv (PrimitiveRingRepresentation.primitiveLinear ℂ g w) =
      M9.PrimitiveStabilizer.primitiveLinear ℂ (toOriginal g) (originalKernelEquiv w) := by
  apply Subtype.ext
  rfl

/-- Literal field-point compatibility in the exact frozen primitive coordinates. -/
theorem primitiveMatrix_coordinates (g : Matrix.symplecticGroup (Fin 3) ℂ)
    (w : M9.ExteriorPrimitive.Primitive ℂ) :
    PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g *ᵥ
        M9.PrimitiveRadicalScheme.primitiveCoordinates w =
      M9.PrimitiveRadicalScheme.primitiveCoordinates
        (M9.PrimitiveStabilizer.primitiveLinear ℂ (toOriginal g) w) := by
  have h := PrimitiveRingCoordinates.primitiveMatrix_coordinates ℂ (RingHom.id ℂ) g
    (originalKernelEquiv.symm w)
  rw [PrimitiveRingCoordinates.primitiveCoordinates_id,
    PrimitiveRingCoordinates.primitiveCoordinates_id,
    originalKernelEquiv_primitiveLinear, LinearEquiv.apply_symm_apply] at h
  exact h

theorem primitiveMatrix_mulVec (g : Matrix.symplecticGroup (Fin 3) ℂ) (v : Fin 14 → ℂ) :
    PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g *ᵥ v =
      M9.PrimitiveRadicalScheme.primitiveCoordinates
        (M9.PrimitiveStabilizer.primitiveLinear ℂ (toOriginal g)
          (M9.PrimitiveRadicalScheme.primitiveCoordinates.symm v)) := by
  simpa only [LinearEquiv.apply_symm_apply] using primitiveMatrix_coordinates g
    (M9.PrimitiveRadicalScheme.primitiveCoordinates.symm v)

theorem primitiveMatrix_fromOriginal (h : M9.PrimitiveStabilizer.Sp6 ℂ)
    (w : M9.ExteriorPrimitive.Primitive ℂ) :
    PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) (fromOriginal h) *ᵥ
        M9.PrimitiveRadicalScheme.primitiveCoordinates w =
      M9.PrimitiveRadicalScheme.primitiveCoordinates
        (M9.PrimitiveStabilizer.primitiveLinear ℂ h w) := by
  simpa only [toOriginal_fromOriginal] using primitiveMatrix_coordinates (fromOriginal h) w

def originalCoordinateLinear (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    (Fin 14 → ℂ) ≃ₗ[ℂ] (Fin 14 → ℂ) :=
  M9.PrimitiveRadicalScheme.primitiveCoordinates.symm.trans
    ((M9.PrimitiveStabilizer.primitiveLinear ℂ h).trans
      M9.PrimitiveRadicalScheme.primitiveCoordinates)

theorem primitiveMatrix_eq_toMatrix (g : Matrix.symplecticGroup (Fin 3) ℂ) :
    PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g =
      LinearMap.toMatrix' (originalCoordinateLinear (toOriginal g)).toLinearMap := by
  have h : Matrix.toLin' (PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) g) =
      (originalCoordinateLinear (toOriginal g)).toLinearMap := by
    apply LinearMap.ext
    exact primitiveMatrix_mulVec g
  have h' := congrArg LinearMap.toMatrix' h
  simpa only [LinearMap.toMatrix'_toLin'] using h'

theorem primitiveMatrix_fromOriginal_eq_toMatrix (h : M9.PrimitiveStabilizer.Sp6 ℂ) :
    PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ) (fromOriginal h) =
      LinearMap.toMatrix' (originalCoordinateLinear h).toLinearMap := by
  rw [primitiveMatrix_eq_toMatrix, toOriginal_fromOriginal]

end M9Native.PrimitiveRingFieldBridge

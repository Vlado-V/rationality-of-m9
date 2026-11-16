module

public import M9StacksIntegration.PrimitiveRingMatrices
public import M9.PrimitiveRadicalScheme

/-!
# Coordinate-ring extension of the frozen primitive chart coordinates

The fixed change of fourteen coordinates is determined by the original
primitive kernel and `PrimitiveRadicalScheme.primitiveCoordinates`. Its
extension to any complex coefficient ring conjugates the actual exterior
representation. In particular it fixes the normalization of the native
Grassmannian action rather than choosing an unrelated fourteen-space.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix Module exteriorPower

namespace M9Native.PrimitiveRingCoordinates

open PrimitiveRingRepresentation

theorem contraction_eq_original :
    LagrangianRing.contraction ℂ = M9.ExteriorPrimitive.contraction ℂ := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change LagrangianRing.contraction ℂ (exteriorPower.ιMulti ℂ 3 v) =
    M9.ExteriorPrimitive.contraction ℂ (exteriorPower.ιMulti ℂ 3 v)
  rw [LagrangianRing.contraction_ιMulti, M9.ExteriorPrimitive.contraction_ιMulti]
  rfl

/-- The kernel is the literal original exterior kernel over the complex field. -/
def originalKernelEquiv : Primitive ℂ ≃ₗ[ℂ] M9.ExteriorPrimitive.Primitive ℂ where
  toFun w := ⟨w.val, by
    change M9.ExteriorPrimitive.contraction ℂ w.val = 0
    rw [← contraction_eq_original]
    exact w.property⟩
  invFun w := ⟨w.val, by
    change LagrangianRing.contraction ℂ w.val = 0
    rw [contraction_eq_original]
    exact w.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The exact fixed coordinate change to the original forty-five-parameter radical chart. -/
def fieldCoordinateChange : (Fin 14 → ℂ) ≃ₗ[ℂ] (Fin 14 → ℂ) :=
  (coordinates ℂ ℂ (RingHom.id ℂ)).symm.trans
    (originalKernelEquiv.trans M9.PrimitiveRadicalScheme.primitiveCoordinates)

def changeMatrix : Matrix (Fin 14) (Fin 14) ℂ :=
  LinearMap.toMatrix' fieldCoordinateChange.toLinearMap

def inverseChangeMatrix : Matrix (Fin 14) (Fin 14) ℂ :=
  LinearMap.toMatrix' fieldCoordinateChange.symm.toLinearMap

theorem changeMatrix_inverse : changeMatrix * inverseChangeMatrix = 1 := by
  rw [changeMatrix, inverseChangeMatrix, ← LinearMap.toMatrix'_comp]
  have h : fieldCoordinateChange.toLinearMap.comp fieldCoordinateChange.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact fieldCoordinateChange.apply_symm_apply
  rw [h, LinearMap.toMatrix'_id]

theorem inverse_changeMatrix : inverseChangeMatrix * changeMatrix = 1 := by
  rw [changeMatrix, inverseChangeMatrix, ← LinearMap.toMatrix'_comp]
  have h : fieldCoordinateChange.symm.toLinearMap.comp fieldCoordinateChange.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact fieldCoordinateChange.symm_apply_apply
  rw [h, LinearMap.toMatrix'_id]

variable (R : Type) [CommRing R] (f : ℂ →+* R)

theorem changeMatrix_inverse_map : changeMatrix.map f * inverseChangeMatrix.map f = 1 := by
  rw [← Matrix.map_mul, changeMatrix_inverse]
  exact Matrix.map_one _ (map_zero f) (map_one f)

theorem inverse_changeMatrix_map : inverseChangeMatrix.map f * changeMatrix.map f = 1 := by
  rw [← Matrix.map_mul, inverse_changeMatrix]
  exact Matrix.map_one _ (map_zero f) (map_one f)

def coefficientChange : (Fin 14 → R) ≃ₗ[R] (Fin 14 → R) :=
  LinearEquiv.ofLinearMap (changeMatrix.map f).mulVecLin
    (inverseChangeMatrix.map f).mulVecLin
    (by
      apply LinearMap.ext
      intro v
      change changeMatrix.map f *ᵥ (inverseChangeMatrix.map f *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, changeMatrix_inverse_map, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro v
      change inverseChangeMatrix.map f *ᵥ (changeMatrix.map f *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, inverse_changeMatrix_map, Matrix.one_mulVec])

/-- Actual primitive coordinates over every complex coefficient ring, with the frozen
field normalization. -/
def primitiveCoordinates : Primitive R ≃ₗ[R] (Fin 14 → R) :=
  (coordinates R ℂ f).trans (coefficientChange R f)

theorem coefficientChange_id : coefficientChange ℂ (RingHom.id ℂ) = fieldCoordinateChange := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  change changeMatrix *ᵥ v = fieldCoordinateChange v
  exact LinearMap.toMatrix'_mulVec _ v

theorem primitiveCoordinates_id (w : Primitive ℂ) :
    primitiveCoordinates ℂ (RingHom.id ℂ) w =
      M9.PrimitiveRadicalScheme.primitiveCoordinates (originalKernelEquiv w) := by
  change coefficientChange ℂ (RingHom.id ℂ) (coordinates ℂ ℂ (RingHom.id ℂ) w) = _
  rw [coefficientChange_id]
  change M9.PrimitiveRadicalScheme.primitiveCoordinates
    (originalKernelEquiv ((coordinates ℂ ℂ (RingHom.id ℂ)).symm
      (coordinates ℂ ℂ (RingHom.id ℂ) w))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The literal matrix of the ring-valued exterior action in the fixed primitive coordinates. -/
def primitiveMatrix (g : Matrix.symplecticGroup (Fin 3) R) : Matrix (Fin 14) (Fin 14) R :=
  changeMatrix.map f * PrimitiveRingMatrices.matrix14 R ℂ f g * inverseChangeMatrix.map f

theorem primitiveMatrix_coordinates (g : Matrix.symplecticGroup (Fin 3) R) (w : Primitive R) :
    primitiveMatrix R f g *ᵥ primitiveCoordinates R f w =
      primitiveCoordinates R f (primitiveLinear R g w) := by
  change (changeMatrix.map f * PrimitiveRingMatrices.matrix14 R ℂ f g *
    inverseChangeMatrix.map f) *ᵥ (changeMatrix.map f *ᵥ coordinates R ℂ f w) =
      changeMatrix.map f *ᵥ coordinates R ℂ f (primitiveLinear R g w)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ (inverseChangeMatrix.map f) (changeMatrix.map f),
    inverse_changeMatrix_map, Matrix.one_mulVec, PrimitiveRingMatrices.matrix14_mulVec]
  change changeMatrix.map f *ᵥ coordinates R ℂ f
    (primitiveLinear R g ((coordinates R ℂ f).symm (coordinates R ℂ f w))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem primitiveMatrix_mulVec (g : Matrix.symplecticGroup (Fin 3) R) (v : Fin 14 → R) :
    primitiveMatrix R f g *ᵥ v =
      primitiveCoordinates R f (primitiveLinear R g ((primitiveCoordinates R f).symm v)) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    primitiveMatrix_coordinates R f g ((primitiveCoordinates R f).symm v)

theorem primitiveMatrix_one : primitiveMatrix R f 1 = 1 := by
  rw [primitiveMatrix, PrimitiveRingMatrices.matrix14_one, Matrix.mul_one, changeMatrix_inverse_map]

theorem primitiveMatrix_mul (g h : Matrix.symplecticGroup (Fin 3) R) :
    primitiveMatrix R f (g*h) = primitiveMatrix R f g * primitiveMatrix R f h := by
  rw [primitiveMatrix, PrimitiveRingMatrices.matrix14_mul, primitiveMatrix, primitiveMatrix]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (inverseChangeMatrix.map f), inverse_changeMatrix_map,
    Matrix.one_mul]

theorem primitiveMatrix_isUnit (g : Matrix.symplecticGroup (Fin 3) R) :
    IsUnit (primitiveMatrix R f g) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_exists_inv.mpr
  refine ⟨(primitiveMatrix R f g⁻¹).det, ?_⟩
  rw [← Matrix.det_mul, ← primitiveMatrix_mul, mul_inv_cancel, primitiveMatrix_one,
    Matrix.det_one]

theorem primitiveMatrix_map {S : Type} [CommRing S] (ρ : R →+* S)
    (g : Matrix.symplecticGroup (Fin 3) R) :
    primitiveMatrix S (ρ.comp f) (LagrangianTransitivity.mapSymplectic R ρ g) =
      (primitiveMatrix R f g).map ρ := by
  simp only [primitiveMatrix, PrimitiveRingMatrices.matrix14_map, Matrix.map_mul, Matrix.map_map]
  rfl

end M9Native.PrimitiveRingCoordinates

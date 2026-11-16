module

public import M9StacksIntegration.PrimitiveAmbientPairing
public import M9StacksIntegration.PrimitiveRingFieldBridge
public import M9StacksIntegration.PrimitiveRhoFiberChart
public import M9StacksIntegration.PrimitiveFamilyFreeAction

/-!
# The original primitive pairing over arbitrary complex coefficient rings

The fixed matrix is the literal Gram matrix of the original exterior
pairing in `PrimitiveRadicalScheme.primitiveCoordinates`. Its invariance
is proved from the actual ring-valued exterior wedge pairing, with no
reducedness or field-valued-points argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

open Module Matrix exteriorPower
open AlgebraicGeometry CategoryTheory

namespace M9Native.PrimitiveRingPairing

open LagrangianRing PrimitiveRingRepresentation
open PrimitiveRingCoordinates PrimitiveRingMatrices

def originalCoordinatePairing : LinearMap.BilinForm ℂ (Fin 14 → ℂ) :=
  (M9.ExteriorPrimitive.primitivePairing ℂ).compl₁₂
    M9.PrimitiveRadicalScheme.primitiveCoordinates.symm.toLinearMap
    M9.PrimitiveRadicalScheme.primitiveCoordinates.symm.toLinearMap

def pairingMatrix : Matrix (Fin 14) (Fin 14) ℂ := originalCoordinatePairing.toMatrix'

theorem pairingMatrix_eq_rhoFiber : pairingMatrix = PrimitiveRhoFiberChart.pairingMatrix := rfl

theorem pairingMatrix_apply (i j : Fin 14) :
    pairingMatrix i j = M9.ExteriorPrimitive.primitivePairing ℂ
      (M9.PrimitiveRadicalScheme.primitiveCoordinates.symm (Pi.single i 1))
      (M9.PrimitiveRadicalScheme.primitiveCoordinates.symm (Pi.single j 1)) := by
  rw [pairingMatrix, LinearMap.BilinForm.toMatrix'_apply]
  rfl

def embeddingBase : Matrix (Fin 20) (Fin 14) ℂ :=
  LagrangianField.embeddingMatrix ℂ * inverseChangeMatrix

variable (R : Type) [CommRing R] (f : ℂ →+* R)

/-- The actual exterior inclusion in the fixed fourteen coordinates. -/
def coordinateEmbedding : (Fin 14 → R) →ₗ[R] Third R :=
  (Primitive R).subtype.comp (primitiveCoordinates R f).symm.toLinearMap

theorem coordinateEmbedding_coordinates (v : Fin 14 → R) :
    (thirdBasis20 R).equivFun (coordinateEmbedding R f v) = embeddingBase.map f *ᵥ v := by
  rw [embeddingBase, Matrix.map_mul, ← Matrix.mulVec_mulVec]
  change (thirdBasis20 R).equivFun
    (embedding R ℂ f (inverseChangeMatrix.map f *ᵥ v)) = _
  exact embedding_coordinates R ℂ f _

theorem coordinateEmbedding_matrix :
    LinearMap.toMatrix (Pi.basisFun R (Fin 14)) (thirdBasis20 R) (coordinateEmbedding R f) =
      embeddingBase.map f := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  have h := congrFun (coordinateEmbedding_coordinates R f (Pi.single j 1)) i
  simpa only [Pi.basisFun_apply, Basis.equivFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] using h

def coordinateForm : LinearMap.BilinForm R (Fin 14 → R) :=
  (PrimitiveAmbientPairing.ambientPairing R).comp (coordinateEmbedding R f) (coordinateEmbedding R f)

theorem coordinateForm_matrix :
    (coordinateForm R f).toMatrix' =
      (embeddingBase.map f).transpose * PrimitiveAmbientPairing.gram R * embeddingBase.map f := by
  change LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin 14))
    ((PrimitiveAmbientPairing.ambientPairing R).comp (coordinateEmbedding R f)
      (coordinateEmbedding R f)) = _
  rw [LinearMap.BilinForm.toMatrix_comp (b := thirdBasis20 R) (c := Pi.basisFun R (Fin 14)),
    coordinateEmbedding_matrix]
  rfl

theorem coordinateEmbedding_id (v : Fin 14 → ℂ) :
    coordinateEmbedding ℂ (RingHom.id ℂ) v =
      (M9.PrimitiveRadicalScheme.primitiveCoordinates.symm v).val := by
  have h : originalKernelEquiv ((primitiveCoordinates ℂ (RingHom.id ℂ)).symm v) =
      M9.PrimitiveRadicalScheme.primitiveCoordinates.symm v := by
    apply M9.PrimitiveRadicalScheme.primitiveCoordinates.injective
    rw [← primitiveCoordinates_id, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact congrArg Subtype.val h

theorem ambientPairing_field :
    PrimitiveAmbientPairing.ambientPairing ℂ = M9.ExteriorPrimitive.ambientPairing ℂ := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change PrimitiveAmbientPairing.ambientPairing ℂ (exteriorPower.ιMulti ℂ 3 v)
    (exteriorPower.ιMulti ℂ 3 w) =
      M9.ExteriorPrimitive.ambientPairing ℂ (exteriorPower.ιMulti ℂ 3 v)
        (exteriorPower.ιMulti ℂ 3 w)
  rw [PrimitiveAmbientPairing.ambientPairing_ιMulti, M9.ExteriorPrimitive.ambientPairing_ιMulti]

theorem coordinateForm_field : coordinateForm ℂ (RingHom.id ℂ) = originalCoordinatePairing := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change PrimitiveAmbientPairing.ambientPairing ℂ (coordinateEmbedding ℂ (RingHom.id ℂ) v)
    (coordinateEmbedding ℂ (RingHom.id ℂ) w) = _
  rw [coordinateEmbedding_id, coordinateEmbedding_id, ambientPairing_field]
  rfl

theorem pairingMatrix_formula :
    pairingMatrix = embeddingBase.transpose * PrimitiveAmbientPairing.gram ℂ * embeddingBase := by
  have h := coordinateForm_matrix ℂ (RingHom.id ℂ)
  rw [coordinateForm_field] at h
  simpa only [pairingMatrix, RingHom.coe_id, Matrix.map_id] using h

theorem coordinateForm_matrix_map : (coordinateForm R f).toMatrix' = pairingMatrix.map f := by
  rw [coordinateForm_matrix, pairingMatrix_formula, Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, ← PrimitiveAmbientPairing.gram_map ℂ f]

/-- The actual exterior inclusion intertwines the ring-valued primitive matrix. -/
theorem coordinateEmbedding_primitiveMatrix (g : Matrix.symplecticGroup (Fin 3) R)
    (v : Fin 14 → R) :
    coordinateEmbedding R f (primitiveMatrix R f g *ᵥ v) =
      exteriorAction R g (coordinateEmbedding R f v) := by
  rw [primitiveMatrix_mulVec]
  change ((primitiveCoordinates R f).symm
    (primitiveCoordinates R f (primitiveLinear R g ((primitiveCoordinates R f).symm v)))).val = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem coordinateForm_natural (g : Matrix.symplecticGroup (Fin 3) R) :
    (coordinateForm R f).comp (primitiveMatrix R f g).mulVecLin
      (primitiveMatrix R f g).mulVecLin = coordinateForm R f := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change PrimitiveAmbientPairing.ambientPairing R
    (coordinateEmbedding R f (primitiveMatrix R f g *ᵥ v))
    (coordinateEmbedding R f (primitiveMatrix R f g *ᵥ w)) =
      PrimitiveAmbientPairing.ambientPairing R (coordinateEmbedding R f v) (coordinateEmbedding R f w)
  rw [coordinateEmbedding_primitiveMatrix, coordinateEmbedding_primitiveMatrix]
  exact LinearMap.congr_fun (LinearMap.congr_fun
    (PrimitiveAmbientPairing.ambientPairing_natural R g) (coordinateEmbedding R f v))
      (coordinateEmbedding R f w)

/-- Exact preservation of the original Gram matrix on every complex coefficient ring. -/
theorem primitiveMatrix_preserves_pairingMatrix (g : Matrix.symplecticGroup (Fin 3) R) :
    (primitiveMatrix R f g).transpose * pairingMatrix.map f * primitiveMatrix R f g =
      pairingMatrix.map f := by
  have h := congrArg LinearMap.BilinForm.toMatrix' (coordinateForm_natural R f g)
  rw [LinearMap.BilinForm.toMatrix'_comp] at h
  have hM : LinearMap.toMatrix' (primitiveMatrix R f g).mulVecLin = primitiveMatrix R f g :=
    LinearMap.toMatrix'_toLin' _
  rw [hM, coordinateForm_matrix_map] at h
  exact h

theorem primitiveMatrix_preserves_rhoPairingMatrix (g : Matrix.symplecticGroup (Fin 3) R) :
    (primitiveMatrix R f g).transpose * PrimitiveRhoFiberChart.pairingMatrix.map f *
      primitiveMatrix R f g = PrimitiveRhoFiberChart.pairingMatrix.map f := by
  rw [← pairingMatrix_eq_rhoFiber]
  exact primitiveMatrix_preserves_pairingMatrix R f g

theorem familyMatrix_preserves_rhoPairingMatrix
    (T : Over PrimitiveFamilyFreeAction.base)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T.left,⊤)) :
    (PrimitiveFamilyFreeAction.familyMatrix T g).transpose *
      PrimitiveRhoFiberChart.pairingMatrix.map (PrimitiveFamilyFreeAction.scalarMap T) *
        PrimitiveFamilyFreeAction.familyMatrix T g =
      PrimitiveRhoFiberChart.pairingMatrix.map (PrimitiveFamilyFreeAction.scalarMap T) :=
  primitiveMatrix_preserves_rhoPairingMatrix _ _ g

end M9Native.PrimitiveRingPairing

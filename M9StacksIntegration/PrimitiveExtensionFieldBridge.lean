module

public import M9StacksIntegration.PrimitiveRingPairing
public import M9StacksIntegration.PrimitiveRadicalNativeScheme

/-!
# Actual primitive kernels and symplectic points over extension fields

The original exterior kernel and original symplectic linear group are
identified over every extension field. The scalar-extension comparison is
characterized by its literal twenty exterior coefficients on pure tensors.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

open Module Matrix exteriorPower
open scoped TensorProduct

namespace M9Native.PrimitiveExtensionFieldBridge

open LagrangianTransitivity

variable (L : Type) [Field L]

theorem contraction_eq_original :
    LagrangianRing.contraction L = M9.ExteriorPrimitive.contraction L := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change LagrangianRing.contraction L (exteriorPower.ιMulti L 3 v) =
    M9.ExteriorPrimitive.contraction L (exteriorPower.ιMulti L 3 v)
  rw [LagrangianRing.contraction_ιMulti, M9.ExteriorPrimitive.contraction_ιMulti]
  rfl

def originalKernelEquiv : PrimitiveRingRepresentation.Primitive L ≃ₗ[L]
    M9.ExteriorPrimitive.Primitive L where
  toFun w := ⟨w.val, by
    change M9.ExteriorPrimitive.contraction L w.val = 0
    rw [← contraction_eq_original L]
    exact w.property⟩
  invFun w := ⟨w.val, by
    change LagrangianRing.contraction L w.val = 0
    rw [contraction_eq_original L]
    exact w.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toOriginal : Matrix.symplecticGroup (Fin 3) L →* M9.PrimitiveStabilizer.Sp6 L where
  toFun g := ⟨symplecticEquiv L g, fun v w => symplecticEquiv_preserves_omega L g v w⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change matrixSix L 1 *ᵥ v = v
    rw [PrimitiveRingRepresentation.matrixSix_one, Matrix.one_mulVec]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change matrixSix L (g*h) *ᵥ v = matrixSix L g *ᵥ (matrixSix L h *ᵥ v)
    rw [PrimitiveRingRepresentation.matrixSix_mul, Matrix.mulVec_mulVec]

theorem splitBasis_repr (v : Fin 6 → L) (i : Fin 3 ⊕ Fin 3) :
    (M9.PrimitiveStabilizer.splitBasis L).repr v i = v (splitIndex i) := by
  cases i <;> rfl

theorem splitBasis_vector (i : Fin 3 ⊕ Fin 3) :
    M9.PrimitiveStabilizer.splitBasis L i = Pi.single (splitIndex i) 1 := by
  cases i with
  | inl i => exact M9.PrimitiveStabilizer.splitBasis_inl L i
  | inr i => exact M9.PrimitiveStabilizer.splitBasis_inr L i

def fromOriginal : M9.PrimitiveStabilizer.Sp6 L →* Matrix.symplecticGroup (Fin 3) L where
  toFun h := ⟨LinearMap.toMatrix (M9.PrimitiveStabilizer.splitBasis L)
    (M9.PrimitiveStabilizer.splitBasis L) h.val.toLinearMap,
    M9.PrimitiveStabilizer.symplectic_matrix L h⟩
  map_one' := by
    apply Subtype.ext
    exact LinearMap.toMatrix_id _
  map_mul' g h := by
    apply Subtype.ext
    exact LinearMap.toMatrix_comp _ _ _ _ _

theorem matrixSix_fromOriginal (h : M9.PrimitiveStabilizer.Sp6 L) :
    matrixSix L (fromOriginal L h) = LinearMap.toMatrix' h.val.toLinearMap := by
  ext i j
  change LinearMap.toMatrix (M9.PrimitiveStabilizer.splitBasis L)
    (M9.PrimitiveStabilizer.splitBasis L) h.val.toLinearMap
      (splitIndex.symm i) (splitIndex.symm j) = _
  rw [LinearMap.toMatrix_apply, splitBasis_repr, splitBasis_vector,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, LinearMap.toMatrix'_apply]

theorem toOriginal_fromOriginal (h : M9.PrimitiveStabilizer.Sp6 L) :
    toOriginal L (fromOriginal L h) = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  change matrixSix L (fromOriginal L h) *ᵥ v = h.val v
  rw [matrixSix_fromOriginal, LinearMap.toMatrix'_mulVec]
  rfl

theorem fromOriginal_toOriginal (g : Matrix.symplecticGroup (Fin 3) L) :
    fromOriginal L (toOriginal L g) = g := by
  apply Subtype.ext
  ext i j
  change LinearMap.toMatrix (M9.PrimitiveStabilizer.splitBasis L)
    (M9.PrimitiveStabilizer.splitBasis L) (toOriginal L g).val.toLinearMap i j = g.val i j
  rw [LinearMap.toMatrix_apply, splitBasis_repr, splitBasis_vector]
  change (matrixSix L g *ᵥ Pi.single (splitIndex j) 1) (splitIndex i) = g.val i j
  rw [Matrix.mulVec_single_one]
  change matrixSix L g (splitIndex i) (splitIndex j) = g.val i j
  simp only [matrixSix, Matrix.submatrix_apply, Equiv.symm_apply_apply]

def originalGroupEquiv : Matrix.symplecticGroup (Fin 3) L ≃* M9.PrimitiveStabilizer.Sp6 L where
  toFun := toOriginal L
  invFun := fromOriginal L
  left_inv := fromOriginal_toOriginal L
  right_inv := toOriginal_fromOriginal L
  map_mul' := (toOriginal L).map_mul

theorem originalKernelEquiv_primitiveLinear (g : Matrix.symplecticGroup (Fin 3) L)
    (w : PrimitiveRingRepresentation.Primitive L) :
    originalKernelEquiv L (PrimitiveRingRepresentation.primitiveLinear L g w) =
      M9.PrimitiveStabilizer.primitiveLinear L (toOriginal L g) (originalKernelEquiv L w) := by
  apply Subtype.ext
  rfl

section ScalarExtension

variable [Algebra ℂ L]

theorem charZero_extension : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℂ L).injective

def fieldCoordinates : M9.ExteriorPrimitive.Primitive L ≃ₗ[L] (Fin 14 → L) :=
  (originalKernelEquiv L).symm.trans
    (PrimitiveRingCoordinates.primitiveCoordinates L (algebraMap ℂ L))

/-- A genuine scalar extension of the original primitive kernel, with its actual exterior
realization over the extension field. -/
def scalarPrimitiveEquiv :
    (L ⊗[ℂ] M9.ExteriorPrimitive.Primitive ℂ) ≃ₗ[L] M9.ExteriorPrimitive.Primitive L :=
  (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates L).trans
    ((PrimitiveRingCoordinates.primitiveCoordinates L (algebraMap ℂ L)).symm.trans
      (originalKernelEquiv L))

theorem scalarPrimitiveEquiv_coordinates (w : L ⊗[ℂ] M9.ExteriorPrimitive.Primitive ℂ) :
    fieldCoordinates L (scalarPrimitiveEquiv L w) =
      PrimitiveRadicalNativeScheme.scalarExtendedCoordinates L w := by
  simp only [fieldCoordinates, scalarPrimitiveEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem scalarPrimitiveEquiv_val (w : L ⊗[ℂ] M9.ExteriorPrimitive.Primitive ℂ) :
    (scalarPrimitiveEquiv L w).val = PrimitiveRingPairing.coordinateEmbedding L
      (algebraMap ℂ L) (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates L w) := rfl

/-- Literal exterior coefficients on every pure tensor characterize the scalar-extension
comparison, including all signs and the original frozen fourteen-coordinate basis. -/
theorem scalarPrimitiveEquiv_tmul_coefficients (a : L) (w : M9.ExteriorPrimitive.Primitive ℂ) :
    (LagrangianRing.thirdBasis20 L).equivFun (scalarPrimitiveEquiv L (a ⊗ₜ[ℂ] w)).val =
      (fun i => algebraMap ℂ L ((LagrangianRing.thirdBasis20 ℂ).equivFun w.val i) * a) := by
  rw [scalarPrimitiveEquiv_val, PrimitiveRingPairing.coordinateEmbedding_coordinates]
  have hE : PrimitiveRingPairing.embeddingBase *ᵥ M9.PrimitiveRadicalScheme.primitiveCoordinates w =
      (LagrangianRing.thirdBasis20 ℂ).equivFun w.val := by
    have h := PrimitiveRingPairing.coordinateEmbedding_coordinates ℂ (RingHom.id ℂ)
      (M9.PrimitiveRadicalScheme.primitiveCoordinates w)
    rw [PrimitiveRingPairing.coordinateEmbedding_id, LinearEquiv.symm_apply_apply] at h
    simpa only [RingHom.coe_id, Matrix.map_id] using h.symm
  have hV : PrimitiveRadicalNativeScheme.scalarExtendedCoordinates L (a ⊗ₜ[ℂ] w) =
      a • ((algebraMap ℂ L) ∘ M9.PrimitiveRadicalScheme.primitiveCoordinates w) := by
    funext i
    rw [PrimitiveRadicalNativeScheme.scalarExtendedCoordinates_tmul]
    change algebraMap ℂ L (M9.PrimitiveRadicalScheme.primitiveCoordinates w i) * a =
      a * algebraMap ℂ L (M9.PrimitiveRadicalScheme.primitiveCoordinates w i)
    exact mul_comm _ _
  rw [hV, Matrix.mulVec_smul]
  funext i
  change a * ((PrimitiveRingPairing.embeddingBase.map (algebraMap ℂ L) *ᵥ
    ((algebraMap ℂ L) ∘ M9.PrimitiveRadicalScheme.primitiveCoordinates w)) i) = _
  rw [← RingHom.map_mulVec, hE]
  exact mul_comm _ _

theorem primitiveMatrix_fieldCoordinates (g : Matrix.symplecticGroup (Fin 3) L)
    (w : M9.ExteriorPrimitive.Primitive L) :
    PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L) g *ᵥ fieldCoordinates L w =
      fieldCoordinates L (M9.PrimitiveStabilizer.primitiveLinear L (toOriginal L g) w) := by
  change PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L) g *ᵥ
    PrimitiveRingCoordinates.primitiveCoordinates L (algebraMap ℂ L) ((originalKernelEquiv L).symm w) =
      PrimitiveRingCoordinates.primitiveCoordinates L (algebraMap ℂ L)
        ((originalKernelEquiv L).symm
          (M9.PrimitiveStabilizer.primitiveLinear L (toOriginal L g) w))
  rw [PrimitiveRingCoordinates.primitiveMatrix_coordinates]
  congr 1

def eRows (K : Type) [Field K] : Matrix (Fin 3) (Fin 6) K :=
  fun i => LagrangianRing.e K i

def fRows (K : Type) [Field K] : Matrix (Fin 3) (Fin 6) K :=
  fun i => LagrangianRing.f K i

theorem rowPlucker_eRows (K : Type) [Field K] :
    LagrangianRing.rowPlucker K (eRows K) = M9.ExteriorPrimitive.a K := by
  unfold LagrangianRing.rowPlucker M9.ExteriorPrimitive.a M9.ExteriorPrimitive.wedge3
  apply congrArg (exteriorPower.ιMulti K 3)
  funext i
  fin_cases i <;> rfl

theorem rowPlucker_fRows (K : Type) [Field K] :
    LagrangianRing.rowPlucker K (fRows K) = M9.ExteriorPrimitive.b K := by
  unfold LagrangianRing.rowPlucker M9.ExteriorPrimitive.b M9.ExteriorPrimitive.wedge3
  apply congrArg (exteriorPower.ιMulti K 3)
  funext i
  fin_cases i <;> rfl

theorem rho_twenty (K : Type) [Field K] :
    (LagrangianRing.thirdBasis20 K).equivFun (M9.PrimitiveStabilizer.rho K).val =
      LagrangianRing.rowTwenty K (eRows K) + LagrangianRing.rowTwenty K (fRows K) := by
  rw [M9.PrimitiveStabilizer.rho_val, map_add, ← rowPlucker_eRows, ← rowPlucker_fRows]
  rfl

theorem rowTwenty_map (M : Matrix (Fin 3) (Fin 6) ℂ) :
    LagrangianRing.rowTwenty L (M.map (algebraMap ℂ L)) =
      (fun i => algebraMap ℂ L (LagrangianRing.rowTwenty ℂ M i)) := by
  funext i
  rw [LagrangianRing.rowTwenty_eq_minor, LagrangianRing.rowTwenty_eq_minor, RingHom.map_det]
  congr 1

theorem eRows_map : (eRows ℂ).map (algebraMap ℂ L) = eRows L := by
  ext i j
  simp only [eRows, Matrix.map_apply, LagrangianRing.e, LagrangianRing.basisVector, Pi.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

theorem fRows_map : (fRows ℂ).map (algebraMap ℂ L) = fRows L := by
  ext i j
  simp only [fRows, Matrix.map_apply, LagrangianRing.f, LagrangianRing.basisVector, Pi.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

/-- The split primitive vector itself is the literal coefficient extension of the original one. -/
theorem rho_coefficients_natural :
    (LagrangianRing.thirdBasis20 L).equivFun (M9.PrimitiveStabilizer.rho L).val =
      (fun i => algebraMap ℂ L
        ((LagrangianRing.thirdBasis20 ℂ).equivFun (M9.PrimitiveStabilizer.rho ℂ).val i)) := by
  rw [rho_twenty, rho_twenty]
  funext i
  change LagrangianRing.rowTwenty L (eRows L) i + LagrangianRing.rowTwenty L (fRows L) i =
    algebraMap ℂ L (LagrangianRing.rowTwenty ℂ (eRows ℂ) i + LagrangianRing.rowTwenty ℂ (fRows ℂ) i)
  rw [map_add]
  have he := congrFun (rowTwenty_map L (eRows ℂ)) i
  rw [eRows_map] at he
  have hf := congrFun (rowTwenty_map L (fRows ℂ)) i
  rw [fRows_map] at hf
  rw [he, hf]

theorem scalarPrimitiveEquiv_rho :
    scalarPrimitiveEquiv L (1 ⊗ₜ[ℂ] M9.PrimitiveStabilizer.rho ℂ) =
      M9.PrimitiveStabilizer.rho L := by
  apply Subtype.ext
  apply (LagrangianRing.thirdBasis20 L).equivFun.injective
  rw [scalarPrimitiveEquiv_tmul_coefficients L, rho_coefficients_natural L]
  funext i
  exact _root_.mul_one (algebraMap ℂ L
    ((LagrangianRing.thirdBasis20 ℂ).equivFun (M9.PrimitiveStabilizer.rho ℂ).val i))

theorem fieldCoordinates_rho :
    fieldCoordinates L (M9.PrimitiveStabilizer.rho L) =
      (fun i => algebraMap ℂ L
        (M9.PrimitiveRadicalScheme.primitiveCoordinates (M9.PrimitiveStabilizer.rho ℂ) i)) := by
  rw [← scalarPrimitiveEquiv_rho L, scalarPrimitiveEquiv_coordinates]
  funext i
  rw [PrimitiveRadicalNativeScheme.scalarExtendedCoordinates_tmul, mul_one]

omit [Algebra ℂ L] in
theorem ambientPairing_field :
    PrimitiveAmbientPairing.ambientPairing L = M9.ExteriorPrimitive.ambientPairing L := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change PrimitiveAmbientPairing.ambientPairing L (exteriorPower.ιMulti L 3 v)
    (exteriorPower.ιMulti L 3 w) =
      M9.ExteriorPrimitive.ambientPairing L (exteriorPower.ιMulti L 3 v)
        (exteriorPower.ιMulti L 3 w)
  rw [PrimitiveAmbientPairing.ambientPairing_ιMulti, M9.ExteriorPrimitive.ambientPairing_ιMulti]

/-- The genuine scalar-extension equivalence also identifies the actual wedge pairings. -/
theorem scalarPrimitiveEquiv_pairing (u v : L ⊗[ℂ] M9.ExteriorPrimitive.Primitive ℂ) :
    M9.ExteriorPrimitive.primitivePairing L (scalarPrimitiveEquiv L u) (scalarPrimitiveEquiv L v) =
      PrimitiveRhoFiberChart.scalarExtendedPairing L u v := by
  rw [PrimitiveRhoFiberChart.scalarExtendedPairing_coordinates]
  have hform : PrimitiveRingPairing.coordinateForm L (algebraMap ℂ L) =
      (PrimitiveRhoFiberChart.pairingMatrix.map (algebraMap ℂ L)).toBilin' := by
    rw [← PrimitiveRingPairing.pairingMatrix_eq_rhoFiber,
      ← PrimitiveRingPairing.coordinateForm_matrix_map, Matrix.toBilin'_toMatrix']
  rw [← hform]
  change M9.ExteriorPrimitive.ambientPairing L (scalarPrimitiveEquiv L u).val
    (scalarPrimitiveEquiv L v).val =
      PrimitiveAmbientPairing.ambientPairing L
        (PrimitiveRingPairing.coordinateEmbedding L (algebraMap ℂ L)
          (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates L u))
        (PrimitiveRingPairing.coordinateEmbedding L (algebraMap ℂ L)
          (PrimitiveRadicalNativeScheme.scalarExtendedCoordinates L v))
  rw [scalarPrimitiveEquiv_val, scalarPrimitiveEquiv_val, ambientPairing_field]

end ScalarExtension

end M9Native.PrimitiveExtensionFieldBridge

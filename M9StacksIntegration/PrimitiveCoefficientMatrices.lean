module

public import M9StacksIntegration.PrimitiveRingMatrices
public import M9StacksIntegration.PrimitiveCoefficientAction
public import M9StacksIntegration.MukaiPrimitiveQuarticAction
public import M9StacksIntegration.MukaiConormalOriginCoordinates

/-! The ring-natural primitive matrices in the original native
primitive basis. In particular the form coordinates use coefficient
duality and the literal transpose, without an alternating-pairing replacement. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open Module Matrix

universe u

namespace M9Native.PrimitiveCoefficientMatrices

open LagrangianField LagrangianPluckerLinear LagrangianTransitivity
open MukaiConormalOriginCoordinates

variable (K : Type u) [Field K] [CharZero K]

theorem coordinates_native (w : PrimitiveRingRepresentation.Primitive K) :
    PrimitiveRingRepresentation.coordinates K K (RingHom.id K) w =
      (primitiveBasis14 K).equivFun (PrimitiveCoefficientAction.primitiveEquiv K w) := by
  change (projectionMatrix K).map (RingHom.id K) *ᵥ
    (LagrangianRing.thirdBasis20 K).equivFun w.val = _
  change projectionMatrix K *ᵥ (LagrangianRing.thirdBasis20 K).equivFun w.val = _
  rw [LagrangianRing.thirdBasis20_eq_field]
  change LinearMap.toMatrix (thirdBasis20 K) (coordinateBasis14 K) (coordinateProjection K) *ᵥ
    (thirdBasis20 K).repr w.val = _
  rw [LinearMap.toMatrix_mulVec_repr,Basis.equivFun_apply,primitiveBasis14,
    Basis.map_repr,LinearEquiv.trans_apply,LagrangianField.primitiveEquiv_symm]
  rfl

/-- The ring-natural representation acts in the exact native fourteen-vector basis. -/
theorem matrix14_native (g : Matrix.symplecticGroup (Fin 3) K) (v : LagrangianField.Primitive K) :
    PrimitiveRingMatrices.matrix14 K K (RingHom.id K) g *ᵥ (primitiveBasis14 K).equivFun v =
      (primitiveBasis14 K).equivFun (PrimitiveCoefficientAction.primitiveAction K g v) := by
  let w := (PrimitiveCoefficientAction.primitiveEquiv K).symm v
  have h : PrimitiveRingRepresentation.coordinates K K (RingHom.id K) w =
      (primitiveBasis14 K).equivFun v := by
    rw [coordinates_native,LinearEquiv.apply_symm_apply]
  rw [← h,PrimitiveRingMatrices.matrix14_mulVec]
  change PrimitiveRingRepresentation.coordinates K K (RingHom.id K)
    (PrimitiveRingRepresentation.primitiveLinear K g
      ((PrimitiveRingRepresentation.coordinates K K (RingHom.id K)).symm
        (PrimitiveRingRepresentation.coordinates K K (RingHom.id K) w))) = _
  rw [LinearEquiv.symm_apply_apply,coordinates_native]
  rfl

theorem matrix14_native_toMatrix (g : Matrix.symplecticGroup (Fin 3) K) :
    PrimitiveRingMatrices.matrix14 K K (RingHom.id K) g =
      LinearMap.toMatrix (primitiveBasis14 K) (primitiveBasis14 K)
        (PrimitiveCoefficientAction.primitiveAction K g).toLinearMap := by
  ext i j
  have h := congrFun (matrix14_native K g (primitiveBasis14 K j)) i
  have hb : (primitiveBasis14 K).equivFun (primitiveBasis14 K j) = Pi.single j 1 := by
    funext k
    by_cases hkj : k=j
    · subst k
      simp only [Basis.equivFun_self,Pi.single_apply,ite_true]
    · simp only [Basis.equivFun_self,Pi.single_apply,ite_eq_right hkj,ite_eq_right (Ne.symm hkj)]
  rw [hb,Matrix.mulVec_single_one] at h
  simpa only [LinearMap.toMatrix_apply,Basis.equivFun_apply,Matrix.col_apply,LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap] using h

/-- The actual primitive form action has the transpose coefficient
matrix in the actual dual basis. This also applies directly to `g⁻¹`. -/
theorem formsCoordinates_quotientMap (g : Matrix.symplecticGroup (Fin 3) K)
    (ell : Module.Dual K (LagrangianField.Primitive K)) :
    formsCoordinates K (MukaiPrimitiveQuartic.quotientMap K (matrixSix K g).mulVecLin ell) =
      (PrimitiveRingMatrices.matrix14 K K (RingHom.id K)
        (LagrangianSigmaInvariance.transposeSymplectic K g)).transpose *ᵥ
          formsCoordinates K ell := by
  funext j
  rw [formsCoordinates_apply,MukaiPrimitiveQuarticAction.quotientMap_eq_dualMap_transpose]
  let a := PrimitiveCoefficientAction.primitiveAction K
    (LagrangianSigmaInvariance.transposeSymplectic K g)
  change ell (a (primitiveBasis14 K j)) = _
  have hs := (primitiveBasis14 K).sum_repr (a (primitiveBasis14 K j))
  rw [← hs,map_sum]
  simp only [map_smul,smul_eq_mul,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_apply,matrix14_native_toMatrix,LinearMap.toMatrix_apply,
    formsCoordinates_apply]
  rfl

end M9Native.PrimitiveCoefficientMatrices

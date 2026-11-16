module

public import M9StacksIntegration.LagrangianExtensionParameterCoordinates
public import M9StacksIntegration.PrimitiveFieldMatrixAction
public import M9StacksIntegration.PrimitiveCoefficientMatrices
public import M9StacksIntegration.LagrangianCoordinateFieldChange

@[expose] public section

/-! The actual native complex-base Sp6 action over EVERY extension field.
The scalar-extended coordinate matrix is derived from the original native
primitive basis. Literal conjugation transports both the actual quotient
point and its original exterior kernel; no action/convention comparison is
assumed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix

namespace M9Native.LagrangianExtensionParameterAction

open LagrangianExtensionParameterCoordinates PrimitiveExtensionFieldBridge

variable (L : Type) [Field L] [Algebra ℂ L]

local instance extensionCharZero : CharZero L := charZero_extension L
local instance primitiveGroup : AddCommGroup (M9.ExteriorPrimitive.Primitive L) :=
  { (M9.ExteriorPrimitive.Primitive L).addCommGroup with
    toAddCommMonoid := (M9.ExteriorPrimitive.Primitive L).addCommMonoid }

/-- The original constant projection is natural under the actual complex
scalar map, so it gives the SAME raw primitive coordinates over L. -/
theorem rawCoordinates_basechange :
    PrimitiveRingRepresentation.coordinates L ℂ (algebraMap ℂ L) =
      PrimitiveRingRepresentation.coordinates L L (RingHom.id L) := by
  apply LinearEquiv.ext
  intro w
  change (LagrangianField.projectionMatrix ℂ).map (algebraMap ℂ L) *ᵥ
      (LagrangianRing.thirdBasis20 L).equivFun w.val =
    (LagrangianField.projectionMatrix L).map (RingHom.id L) *ᵥ
      (LagrangianRing.thirdBasis20 L).equivFun w.val
  rw [LagrangianCoordinateFieldChange.projectionMatrix_map (algebraMap ℂ L)] <;> rfl

theorem rawCoordinates_native (w : PrimitiveRingRepresentation.Primitive L) :
    PrimitiveRingRepresentation.coordinates L ℂ (algebraMap ℂ L) w =
      (LagrangianPluckerLinear.primitiveBasis14 L).equivFun
        (PrimitiveCoefficientAction.primitiveEquiv L w) := by
  rw [rawCoordinates_basechange L]
  exact PrimitiveCoefficientMatrices.coordinates_native L w

/-- This pins the frozen original exterior-kernel coordinates to C_L
times the actual native primitive-basis coordinates. -/
theorem fieldCoordinates_native (w : M9.ExteriorPrimitive.Primitive L) :
    fieldCoordinates L w =
      PrimitiveRingCoordinates.changeMatrix.map (algebraMap ℂ L) *ᵥ
        (LagrangianPluckerLinear.primitiveBasis14 L).equivFun
          (PrimitiveCoefficientAction.primitiveEquiv L ((originalKernelEquiv L).symm w)) := by
  change PrimitiveRingCoordinates.changeMatrix.map (algebraMap ℂ L) *ᵥ
    PrimitiveRingRepresentation.coordinates L ℂ (algebraMap ℂ L)
      ((originalKernelEquiv L).symm w) = _
  rw [rawCoordinates_native L]

theorem matrix14_basechange (g : Matrix.symplecticGroup (Fin 3) L) :
    PrimitiveRingMatrices.matrix14 L ℂ (algebraMap ℂ L) g =
      PrimitiveRingMatrices.matrix14 L L (RingHom.id L) g := by
  rw [PrimitiveRingMatrices.matrix14_eq_toMatrix, PrimitiveRingMatrices.matrix14_eq_toMatrix]
  simp only [PrimitiveRingMatrices.coordinateLinear, rawCoordinates_basechange L]

def rawMatrix (g : Matrix.symplecticGroup (Fin 3) L) : Matrix (Fin 14) (Fin 14) L :=
  PrimitiveRingMatrices.matrix14 L L (RingHom.id L) g

/-- The genuine ring-natural original primitive matrix is C_L raw(g) C_L^{-1}. -/
theorem primitiveMatrix_conjugate (g : Matrix.symplecticGroup (Fin 3) L) :
    PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L) g =
      PrimitiveRingCoordinates.changeMatrix.map (algebraMap ℂ L) * rawMatrix L g *
        PrimitiveRingCoordinates.inverseChangeMatrix.map (algebraMap ℂ L) := by
  rw [PrimitiveRingCoordinates.primitiveMatrix, matrix14_basechange L] <;> rfl

theorem coordinateMatrix_toOriginal (g : Matrix.symplecticGroup (Fin 3) L) :
    PrimitiveFieldMatrixAction.coordinateMatrix L (toOriginal L g) =
      PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L) g := by
  rw [PrimitiveFieldMatrixAction.coordinateMatrix, fromOriginal_toOriginal]

theorem coordinateMatrix_toOriginal_inv (g : Matrix.symplecticGroup (Fin 3) L) :
    PrimitiveFieldMatrixAction.coordinateMatrix L (toOriginal L g)⁻¹ =
      PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L) g⁻¹ := by
  rw [← map_inv (toOriginal L) g, coordinateMatrix_toOriginal L]

def rawActedMatrix (g : Matrix.symplecticGroup (Fin 3) L)
    (M : Matrix (Fin 5) (Fin 14) L) : Matrix (Fin 5) (Fin 14) L :=
  M * rawMatrix L g⁻¹

theorem rawActed_surjective (g : Matrix.symplecticGroup (Fin 3) L)
    (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec) :
    Function.Surjective (rawActedMatrix L g M).mulVec := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨rawMatrix L g * SplitMatrixGrassmannian.fieldRightInverse 9 14 L M hM, ?_⟩
  have hi : rawMatrix L g⁻¹ * rawMatrix L g = 1 := by
    dsimp only [rawMatrix]
    rw [← PrimitiveRingMatrices.matrix14_mul, inv_mul_cancel, PrimitiveRingMatrices.matrix14_one]
  change M * rawMatrix L g⁻¹ *
    (rawMatrix L g * SplitMatrixGrassmannian.fieldRightInverse 9 14 L M hM) = 1
  calc
    _ = M * (rawMatrix L g⁻¹ * rawMatrix L g) *
      SplitMatrixGrassmannian.fieldRightInverse 9 14 L M hM := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hi, Matrix.mul_one]
      exact SplitMatrixGrassmannian.fieldRightInverse_spec 9 14 L M hM

theorem originalMatrix_rawActed (g : Matrix.symplecticGroup (Fin 3) L)
    (M : Matrix (Fin 5) (Fin 14) L) :
    originalMatrix L (rawActedMatrix L g M) =
      originalMatrix L M * PrimitiveFieldMatrixAction.coordinateMatrix L (toOriginal L g)⁻¹ := by
  rw [coordinateMatrix_toOriginal_inv L, primitiveMatrix_conjugate L]
  dsimp only [originalMatrix, rawActedMatrix]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (PrimitiveRingCoordinates.inverseChangeMatrix.map (algebraMap ℂ L)),
    PrimitiveRingCoordinates.inverse_changeMatrix_map, Matrix.one_mul]

def originalKernel (M : Matrix (Fin 5) (Fin 14) L) :
    Submodule L (M9.ExteriorPrimitive.Primitive L) :=
  (Matrix.toLin' (originalMatrix L M)).ker.map (fieldCoordinates L).symm.toLinearMap

/-- Actual transport in the original exterior primitive kernel, with the
original linear action and its exact inverse-precomposition convention. -/
theorem originalKernel_rawActed (g : Matrix.symplecticGroup (Fin 3) L)
    (M : Matrix (Fin 5) (Fin 14) L) :
    originalKernel L (rawActedMatrix L g M) =
      (originalKernel L M).map
        (M9.PrimitiveStabilizer.primitiveLinear L (toOriginal L g)).toLinearMap := by
  dsimp only [originalKernel]
  rw [originalMatrix_rawActed L]
  exact PrimitiveFieldMatrixAction.actedKernel_original L (toOriginal L g) (originalMatrix L M)

/-- Equality of the ACTUAL native group-scheme action on the original
complex-base field point. All matrix classes and coordinate changes are derived. -/
theorem native_action_originalPoint (g : Matrix.symplecticGroup (Fin 3) L)
    (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec) :
    PrimitiveFieldMatrixAction.actPoint L (toOriginal L g) (originalPoint L M hM)
      (originalPoint_projection L M hM) =
        originalPoint L (rawActedMatrix L g M) (rawActed_surjective L g M hM) := by
  exact PrimitiveFieldMatrixAction.actPoint_eq_of_original_kernel_transport L (toOriginal L g)
    (originalPoint L M hM)
    (originalPoint L (rawActedMatrix L g M) (rawActed_surjective L g M hM))
    (originalPoint_projection L M hM)
    (originalPoint_projection L (rawActedMatrix L g M) (rawActed_surjective L g M hM))
    (originalMatrix L M) (originalMatrix L (rawActedMatrix L g M))
    (originalMatrix_surjective L M hM)
    (originalMatrix_surjective L (rawActedMatrix L g M) (rawActed_surjective L g M hM))
    (originalPoint_class L M hM)
    (originalPoint_class L (rawActedMatrix L g M) (rawActed_surjective L g M hM))
    (originalKernel_rawActed L g M)

/-- The incidence client's literal raw row-span calculation suffices for
the genuine original-C native Sp6 orbit equality over every extension L. -/
theorem native_action_eq_of_rowSpan_eq (g : Matrix.symplecticGroup (Fin 3) L)
    (M N : Matrix (Fin 5) (Fin 14) L)
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (h : LagrangianParameterFieldMatrixAction.rowSpan L
        (M * PrimitiveRingMatrices.matrix14 L L (RingHom.id L) g⁻¹) =
      LagrangianParameterFieldMatrixAction.rowSpan L N) :
    PrimitiveFieldMatrixAction.actPoint L (toOriginal L g) (originalPoint L M hM)
      (originalPoint_projection L M hM) = originalPoint L N hN :=
  (native_action_originalPoint L g M hM).trans
    (originalPoint_eq_of_rowSpan_eq L (rawActedMatrix L g M) N
      (rawActed_surjective L g M hM) hN h)

end M9Native.LagrangianExtensionParameterAction

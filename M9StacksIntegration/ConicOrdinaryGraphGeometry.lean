module

public import M9StacksIntegration.ConicMovingFrameBaseChange
public import M9StacksIntegration.ConicConstantActionMatrices

/-! Original ordinary graphs in actual moving conic frames. All graph
kernels are the native split quotient matrices in the fixed conic coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Matrix
open scoped Classical

namespace M9Native.ConicOrdinaryGraphGeometry

open M9.GraphBundleDescent M9.MovingDeterminantFrames
open M9.DeterminantFrameScalarExtension M9.PrimitiveTwistedReduced
open ConicFrameHeadMatrices MovingConicCells ConicConstantActionMatrices
open GraphGrassmannianChart

variable (K : Type*) [Field K] [Algebra ℂ K] [CharZero K]

local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

def frameMap (F : GL3 K) : Head K →ₗ[K] M9.Symmetric3 K :=
  (congruenceEquiv K F).toLinearMap.comp
    ((standardPlane K).subtype.comp (standardPlaneBasis K).equivFun.symm.toLinearMap)

omit [CharZero K] in
theorem frameMap_coordinates (F : GL3 K) (x : Head K) :
    ConicCompatibleGraphCoordinates.conicSplit K (frameMap K F x) =
      ((headMatrix K F).mulVec x, (tailMatrix K F).mulVec x) := by
  apply Prod.ext
  · simpa only [frameMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Submodule.subtype_apply] using
      MovingConicCells.head_formula K F ((standardPlaneBasis K).equivFun.symm x)
  · simpa only [frameMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Submodule.subtype_apply] using
      MovingConicCells.tail_formula K F ((standardPlaneBasis K).equivFun.symm x)

def framedEmbedding (F H : GL3 K) (Z : GL4 K) : Head K →ₗ[K] (Fin 12 → K) :=
  (pairCoordinates K).toLinearMap.comp
    ((frameMap K F).prod ((frameMap K H).comp Z.val.mulVecLin))

def ordinaryIsomorphism (F H : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det)
    (Z : GL4 K) : GL4 K :=
  headUnit K H hH * Z * (headUnit K F hF)⁻¹

def ordinaryQuotient (F H : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det)
    (Z : GL4 K) : Matrix (Fin 8) (Fin 12) K :=
  kernelMatrix (blockRows (movingCellMatrix K F hF) (ordinaryIsomorphism K F H hF hH Z).val
    (movingCellMatrix K H hH * (ordinaryIsomorphism K F H hF hH Z).val))

theorem framedEmbedding_graph (F H : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det)
    (Z : GL4 K) (x : Head K) :
    framedEmbedding K F H Z x = ambientCoordinates
      (graphFamilyEmbedding K (movingCellMatrix K F hF) (movingCellMatrix K H hH)
        (ordinaryIsomorphism K F H hF hH Z) ((headUnit K F hF).val.mulVec x)) := by
  change pairCoordinates K (frameMap K F x, frameMap K H (Z.val.mulVec x)) = _
  rw [pairCoordinates_apply, frameMap_coordinates, frameMap_coordinates,
    graphFamilyEmbedding_apply]
  apply congrArg (ambientCoordinates (R := K))
  have hi : (headUnit K F hF)⁻¹.val.mulVec ((headUnit K F hF).val.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hx : (ordinaryIsomorphism K F H hF hH Z).val.mulVec
      ((headUnit K F hF).val.mulVec x) = (headUnit K H hH).val.mulVec (Z.val.mulVec x) := by
    change ((headUnit K H hH).val * Z.val * (headUnit K F hF)⁻¹.val).mulVec _ = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hi]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change (tailMatrix K F).mulVec x =
        ((tailMatrix K F) * (headUnit K F hF)⁻¹.val).mulVec _
      rw [← Matrix.mulVec_mulVec, hi]
  · apply Prod.ext
    · exact hx.symm
    · change (tailMatrix K H).mulVec (Z.val.mulVec x) =
        ((tailMatrix K H * (headUnit K H hH)⁻¹.val) *
          (ordinaryIsomorphism K F H hF hH Z).val).mulVec _
      have hh : (headUnit K H hH)⁻¹.val.mulVec
          ((headUnit K H hH).val.mulVec (Z.val.mulVec x)) = Z.val.mulVec x := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, hx, ← Matrix.mulVec_mulVec, hh]

/-- Exact equality between the actual native quotient kernel and the
actual moving-frame graph, proved without a dimension premise. -/
theorem ordinaryQuotient_kernel (F H : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det)
    (Z : GL4 K) :
    LinearMap.ker (ordinaryQuotient K F H hF hH Z).mulVecLin =
      LinearMap.range (framedEmbedding K F H Z) := by
  change LinearMap.ker (Matrix.toLin' (kernelMatrix (blockRows
    (movingCellMatrix K F hF) (ordinaryIsomorphism K F H hF hH Z).val
    (movingCellMatrix K H hH * (ordinaryIsomorphism K F H hF hH Z).val)))) = _
  rw [kernel_eq_actualGraph]
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(headUnit K F hF)⁻¹.val.mulVec x, ?_⟩
    rw [framedEmbedding_graph K F H hF hH Z _,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rfl
  · rintro ⟨x, rfl⟩
    exact ⟨(headUnit K F hF).val.mulVec x, (framedEmbedding_graph K F H hF hH Z x).symm⟩

end M9Native.ConicOrdinaryGraphGeometry

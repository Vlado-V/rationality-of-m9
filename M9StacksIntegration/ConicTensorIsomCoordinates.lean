module

public import M9StacksIntegration.DualConicTensorCoordinates

/-! The actual moving isomorphism fibre in literal matrix coordinates. Its
native determinant-twisted cell matrix is β(H) Z β(F)⁻¹, where Z is the actual
original scalar-extended E₀ isomorphism coordinate. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

open scoped TensorProduct

namespace M9Native.ConicTensorIsomCoordinates

open M9.GraphBundleDescent

section Generic
variable {K R E F : Type*} [Field K]
  [AddCommGroup R] [Module K R] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- Change of two actual frames, proved on vectors before it is used for
any moving geometric subspace. -/
theorem framedMatrix_change (r : R ≃ₗ[K] Head K) (p : R ≃ₗ[K] E) (q : R ≃ₗ[K] F)
    (c : E ≃ₗ[K] Head K) (d : F ≃ₗ[K] Head K) (L N : GL4 K)
    (hp : p.trans c = r.trans (matrixLinearEquiv K L))
    (hq : q.trans d = r.trans (matrixLinearEquiv K N)) (f : E ≃ₗ[K] F) :
    (matrixLinearEquiv K).symm (c.symm.trans (f.trans d)) =
      N * (matrixLinearEquiv K).symm
        (r.symm.trans (p.trans (f.trans (q.symm.trans r)))) * L⁻¹ := by
  let l := matrixLinearEquiv K L
  let n := matrixLinearEquiv K N
  have hpv (x : R) : c (p x) = l (r x) := LinearEquiv.congr_fun hp x
  have hqv (x : R) : d (q x) = n (r x) := LinearEquiv.congr_fun hq x
  apply (matrixLinearEquiv K).injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  apply LinearEquiv.ext
  intro v
  have hc : c.symm v = p (r.symm (l.symm v)) := by
    apply c.injective
    calc
      c (c.symm v) = v := c.apply_symm_apply v
      _ = l (r (r.symm (l.symm v))) :=
        (l.apply_symm_apply v).symm.trans
          (congrArg l (r.apply_symm_apply (l.symm v))).symm
      _ = c (p (r.symm (l.symm v))) := (hpv _).symm
  have hd : d (f (p (r.symm (l.symm v)))) =
      n (r (q.symm (f (p (r.symm (l.symm v)))))) := by
    have h := hqv (q.symm (f (p (r.symm (l.symm v)))))
    exact (congrArg d (q.apply_symm_apply _)).symm.trans h
  change d (f (c.symm v)) = n (r (q.symm (f (p (r.symm (l.symm v))))))
  exact (congrArg (fun x => d (f x)) hc).trans hd

end Generic

open M9.StandardFourPlaneRepresentation M9.MovingDeterminantFrames M9.MovingDualDeterminantFrames
open M9.DeterminantFrameScalarExtension M9.DeterminantFrameScalarEquivariance
open M9.MovingScalarExtendedGraphFrames
open MovingConicTensorCoordinates DualConicTensorCoordinates ConicFrameHeadMatrices

variable (K : Type*) [Field K] [Algebra ℂ K] [CharZero K]

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }
local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }
local instance dualPlaneGroup (S : Submodule K (Module.Dual K (M9.Symmetric3 K))) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

def rawMatrix (F H : GL3 K)
    (f : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) : GL4 K :=
  (matrixLinearEquiv K).symm
    ((rawCoordinates K).symm.trans ((rawIsomCoordinates K F H f).trans (rawCoordinates K)))

def cellMatrix (F H : GL3 K) (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det)
    (f : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) : GL4 K :=
  (matrixLinearEquiv K).symm
    ((cellTensorCoordinates K F hF).symm.trans (f.trans (dualCellTensorCoordinates K H hH)))

/-- The actual graph-fibre frame formula, retaining the genuine moving
source and genuine trace-dual target. -/
theorem cellMatrix_eq_compensated (F H : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hH : IsUnit (headMatrix K H).det)
    (f : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) :
    cellMatrix K F H hF hH f =
      compensatedHead K H hH * rawMatrix K F H f * (compensatedHead K F hF)⁻¹ := by
  exact framedMatrix_change (rawCoordinates K) (rawMovingFrame K F) (rawDualMovingFrame K H)
    (cellTensorCoordinates K F hF) (dualCellTensorCoordinates K H hH)
    (compensatedHead K F hF) (compensatedHead K H hH)
    (sourceFrame_coordinates K F hF) (targetFrame_coordinates K H hH) f

end M9Native.ConicTensorIsomCoordinates

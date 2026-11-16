module

public import M9.MovingDualDeterminantFrames

/-! Swapping the actual moving graph factors gives matrix inversion. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
open scoped Classical TensorProduct

namespace M9.MovingGraphSwap
open MovingDeterminantFrames MovingDualDeterminantFrames

section Generic
variable {K A B U V U' V' : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V']

theorem framedIsom_swap (p : A ≃ₗ[K] U) (q : B ≃ₗ[K] V)
    (s : U ≃ₗ[K] U') (t : V ≃ₗ[K] V') (x : U ≃ₗ[K] V') :
    q.trans ((t.trans (x.symm.trans s)).trans (p.trans s).symm) =
      (p.trans (x.trans (q.trans t).symm)).symm := by
  apply LinearEquiv.ext
  intro v
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]

end Generic

variable (K : Type*) [Field K] [CharZero K]

local instance planeGroup (S : Submodule K (Q K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }
local instance dualPlaneGroup (S : Submodule K (Module.Dual K (Q K))) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

/-- The actual trace identification, tensored with its actual dual top
exterior transport. -/
def traceTensor (S : Submodule K (Q K)) (F : GL3 K) :
    Twisted K (movingPlane K S F) ≃ₗ[K] Twisted K (dualMovingPlane K S F) :=
  tensorTransport (tracePlaneFrame K S F)

/-- Exchange of the actual two graph factors after their literal trace
identification. -/
def swapIsom (S T : Submodule K (Q K)) (F H : GL3 K)
    (x : Twisted K (movingPlane K S F) ≃ₗ[K] Twisted K (dualMovingPlane K T H)) :
    Twisted K (movingPlane K T H) ≃ₗ[K] Twisted K (dualMovingPlane K S F) :=
  (traceTensor K T H).trans (x.symm.trans (traceTensor K S F))

/-- For the original compensated tensor frames, actual graph exchange is
exactly inverse, including all determinant normalizations. -/
theorem normalizedIsomCoordinates_swap (S T : Submodule K (Q K)) (F H : GL3 K)
    (x : Twisted K (movingPlane K S F) ≃ₗ[K] Twisted K (dualMovingPlane K T H)) :
    normalizedIsomCoordinates K T S H F (swapIsom K S T F H x) =
      (normalizedIsomCoordinates K S T F H x).symm := by
  exact framedIsom_swap (compensatedFrame K S F) (compensatedFrame K T H)
    (traceTensor K S F) (traceTensor K T H) x

end M9.MovingGraphSwap

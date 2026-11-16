module

public import M9.DeterminantFrameScalarEquivariance
public import M9.MovingGammaGraphCoordinates
public import M9.MovingGraphSwap

/-! Actual moving graph frames with the literal scalar-extended E0 source. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
open scoped Classical TensorProduct

namespace M9.MovingScalarExtendedGraphFrames
open Module StandardFourPlaneRepresentation MovingDeterminantFrames MovingDualDeterminantFrames
open DeterminantFrameScalarExtension DeterminantFrameScalarEquivariance TetrahedralGroup

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

variable (K : Type*) [Field K] [Algebra ℂ K] [CharZero K]

local instance planeGroup (S : Submodule K (Q K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }
local instance dualPlaneGroup (S : Submodule K (Module.Dual K (Q K))) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

/-- The actual trace-dual moving tensor, framed by the original K tensor E0. -/
def rawDualMovingFrame (H : GL3 K) :
    (K ⊗[ℂ] E0) ≃ₗ[K] Twisted K (dualMovingPlane K (standardPlane K) H) :=
  (rawToTwisted K).trans (dualCompensatedFrame K (standardPlane K) H)

def sourceIdentification (g : Gamma) (F : GL3 K) :
    Twisted K (movingPlane K (standardPlane K) (F * constantGamma K g)) ≃ₗ[K]
      Twisted K (movingPlane K (standardPlane K) F) :=
  tensorTransport (planeEquivOfEq K (movingPlane_right K (standardPlane K)
    (constantGamma K g) F (constantGamma_plane K g)))

def targetIdentification (g : Gamma) (H : GL3 K) :
    Twisted K (dualMovingPlane K (standardPlane K) (H * constantGamma K g)) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H) :=
  tensorTransport (dualPlaneEquivOfEq K (dualMovingPlane_eq K (standardPlane K) _ H
    (movingPlane_right K (standardPlane K) (constantGamma K g) H (constantGamma_plane K g))))

theorem rawDualMovingFrame_right_gamma (g : Gamma) (H : GL3 K) :
    (rawDualMovingFrame K (H * constantGamma K g)).trans (targetIdentification K g H) =
      (rawGamma K g).trans (rawDualMovingFrame K H) := by
  have ht := dualCompensatedFrame_right K (standardPlane K) (constantGamma K g) H
    (constantGamma_plane K g) (constantGamma_det K g)
  rw [constantGamma_stabilizer] at ht
  apply LinearEquiv.ext
  intro x
  have hp := LinearEquiv.congr_fun ht (rawToTwisted K x)
  change _ = dualCompensatedFrame K (standardPlane K) H
    (rawToTwisted K (rawGamma K g x))
  rw [rawToTwisted_gamma]
  exact hp

omit [CharZero K] in
theorem rawMovingFrame_scalar (a : Kˣ) (F : GL3 K) :
    (rawMovingFrame K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F)).trans
        (tensorTransport (planeEquivOfEq K (movingPlane_scalar K (standardPlane K) a F))) =
      rawMovingFrame K F := by
  apply LinearEquiv.ext
  intro x
  exact LinearEquiv.congr_fun
    (compensatedFrame_scalar K (standardPlane K) (standardPlaneBasis K) a F)
    (rawToTwisted K x)

theorem rawDualMovingFrame_scalar (a : Kˣ) (H : GL3 K) :
    (rawDualMovingFrame K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * H)).trans
        (tensorTransport (dualPlaneEquivOfEq K (dualMovingPlane_eq K (standardPlane K) _ H
          (movingPlane_scalar K (standardPlane K) a H)))) =
      rawDualMovingFrame K H := by
  apply LinearEquiv.ext
  intro x
  exact LinearEquiv.congr_fun
    (dualCompensatedFrame_scalar K (standardPlane K) (standardPlaneBasis K) a H)
    (rawToTwisted K x)

omit [CharZero K] in
theorem rawMovingFrame_connected (g F : GL3 K) :
    (rawMovingFrame K F).trans (connectedTensorTransport K (standardPlane K) g F) =
      rawMovingFrame K (g*F) := by
  apply LinearEquiv.ext
  intro x
  exact LinearEquiv.congr_fun (compensatedFrame_connected K (standardPlane K) g F)
    (rawToTwisted K x)

theorem rawDualMovingFrame_connected (g H : GL3 K) :
    (rawDualMovingFrame K H).trans (dualConnectedTensorTransport K (standardPlane K) g H) =
      rawDualMovingFrame K (FrameAction.contragredient g * H) := by
  apply LinearEquiv.ext
  intro x
  exact LinearEquiv.congr_fun (dualCompensatedFrame_connected K (standardPlane K) g H)
    (rawToTwisted K x)

/-- Coordinates of an actual graph isomorphism on the literal K tensor E0. -/
def rawIsomCoordinates (F H : GL3 K)
    (x : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) :
    (K ⊗[ℂ] E0) ≃ₗ[K] (K ⊗[ℂ] E0) :=
  (rawMovingFrame K F).trans (x.trans (rawDualMovingFrame K H).symm)

theorem rawIsomCoordinates_normalized (F H : GL3 K)
    (x : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) :
    rawIsomCoordinates K F H x = (rawToTwisted K).trans
      ((normalizedIsomCoordinates K (standardPlane K) (standardPlane K) F H x).trans
        (rawToTwisted K).symm) := rfl

def rightIsomTransport (a b : Gamma) (F H : GL3 K)
    (x : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) :
    Twisted K (movingPlane K (standardPlane K) (F * constantGamma K a)) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) (H * constantGamma K b)) :=
  (sourceIdentification K a F).trans (x.trans (targetIdentification K b H).symm)

/-- Actual right-deck changes, with the original scalar-extended finite
representation on both graph-coordinate factors. -/
theorem rawIsomCoordinates_right (a b : Gamma) (F H : GL3 K)
    (x : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) :
    rawIsomCoordinates K (F * constantGamma K a) (H * constantGamma K b)
      (rightIsomTransport K a b F H x) =
      (rawGamma K a).trans ((rawIsomCoordinates K F H x).trans (rawGamma K b).symm) := by
  exact MovingGammaGraphCoordinates.framedIsom_right
    (rawMovingFrame K F) (rawDualMovingFrame K H)
    (rawMovingFrame K (F * constantGamma K a)) (rawDualMovingFrame K (H * constantGamma K b))
    (sourceIdentification K a F) (targetIdentification K b H)
    (rawGamma K a) (rawGamma K b) x
    (rawMovingFrame_right_gamma K a F) (rawDualMovingFrame_right_gamma K b H)

theorem rawIsomCoordinates_connected (g F H : GL3 K)
    (x : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) :
    rawIsomCoordinates K (g*F) (FrameAction.contragredient g * H)
      (connectedIsomTransport K (standardPlane K) (standardPlane K) g F H x) =
      rawIsomCoordinates K F H x := by
  have he := framedIsom_transport (rawMovingFrame K F) (rawDualMovingFrame K H)
    (connectedTensorTransport K (standardPlane K) g F)
    (dualConnectedTensorTransport K (standardPlane K) g H) x
  simpa only [rawMovingFrame_connected, rawDualMovingFrame_connected,
    rawIsomCoordinates, connectedIsomTransport] using he

/-- Literal graph exchange in the original scalar-extended E0 coordinates
is inverse, including both actual trace and determinant transports. -/
theorem rawIsomCoordinates_swap (F H : GL3 K)
    (x : Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K]
      Twisted K (dualMovingPlane K (standardPlane K) H)) :
    rawIsomCoordinates K H F
      (MovingGraphSwap.swapIsom K (standardPlane K) (standardPlane K) F H x) =
      (rawIsomCoordinates K F H x).symm := by
  exact MovingGraphSwap.framedIsom_swap (rawMovingFrame K F) (rawMovingFrame K H)
    (MovingGraphSwap.traceTensor K (standardPlane K) F)
    (MovingGraphSwap.traceTensor K (standardPlane K) H) x

end M9.MovingScalarExtendedGraphFrames

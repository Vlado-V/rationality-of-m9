module

public import M9.MovingDualDeterminantFrames

/-! Actual right-frame changes on normalized graph isomorphism coordinates. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
open scoped Classical TensorProduct

namespace M9.MovingGammaGraphCoordinates
open MovingDeterminantFrames MovingDualDeterminantFrames

section Generic
variable {K A B U V U' V' : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V']

theorem framedIsom_right (p : A ≃ₗ[K] U) (q : B ≃ₗ[K] V)
    (p' : A ≃ₗ[K] U') (q' : B ≃ₗ[K] V') (j : U' ≃ₗ[K] U) (k : V' ≃ₗ[K] V)
    (a : A ≃ₗ[K] A) (b : B ≃ₗ[K] B) (x : U ≃ₗ[K] V)
    (hp : p'.trans j = a.trans p) (hq : q'.trans k = b.trans q) :
    p'.trans ((j.trans (x.trans k.symm)).trans q'.symm) = a.trans ((p.trans (x.trans q.symm)).trans b.symm) := by
  change (p'.trans j).trans (x.trans (q'.trans k).symm) = _
  rw [hp,hq]
  rfl

end Generic

open StandardFourPlaneRepresentation TetrahedralGroup

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }
local instance symPlaneGroup (S : Submodule ℂ (Q ℂ)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }
local instance dualPlaneGroup (S : Submodule ℂ (Module.Dual ℂ (Q ℂ))) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

def sourceIdentification (g : Gamma) (F : GL3 ℂ) :
    Twisted ℂ (movingPlane ℂ S0 (F * FrameAction.tetrahedralGL g)) ≃ₗ[ℂ] Twisted ℂ (movingPlane ℂ S0 F) :=
  tensorTransport (planeEquivOfEq ℂ (movingPlane_right ℂ S0 (FrameAction.tetrahedralGL g) F (gammaPlane_eq g)))

def targetIdentification (g : Gamma) (H : GL3 ℂ) :
    Twisted ℂ (dualMovingPlane ℂ S0 (H * FrameAction.tetrahedralGL g)) ≃ₗ[ℂ]
      Twisted ℂ (dualMovingPlane ℂ S0 H) :=
  tensorTransport (dualPlaneEquivOfEq ℂ (dualMovingPlane_eq ℂ S0 _ H
    (movingPlane_right ℂ S0 (FrameAction.tetrahedralGL g) H (gammaPlane_eq g))))

def rightIsomTransport (a b : Gamma) (F H : GL3 ℂ)
    (x : Twisted ℂ (movingPlane ℂ S0 F) ≃ₗ[ℂ] Twisted ℂ (dualMovingPlane ℂ S0 H)) :
    Twisted ℂ (movingPlane ℂ S0 (F * FrameAction.tetrahedralGL a)) ≃ₗ[ℂ]
      Twisted ℂ (dualMovingPlane ℂ S0 (H * FrameAction.tetrahedralGL b)) :=
  (sourceIdentification a F).trans (x.trans (targetIdentification b H).symm)

/-- Under literal right-frame substitutions F↦Fa, H↦Hb, normalized graph
coordinates are sent to ρ(b)⁻¹ X ρ(a), with both ρ the actual E0 tensor
representations used by finite Galois descent. -/
theorem normalizedIsomCoordinates_right (a b : Gamma) (F H : GL3 ℂ)
    (x : Twisted ℂ (movingPlane ℂ S0 F) ≃ₗ[ℂ] Twisted ℂ (dualMovingPlane ℂ S0 H)) :
    normalizedIsomCoordinates ℂ S0 S0 (F * FrameAction.tetrahedralGL a) (H * FrameAction.tetrahedralGL b)
        (rightIsomTransport a b F H x) =
      (tensorRepresentation a).trans
        ((normalizedIsomCoordinates ℂ S0 S0 F H x).trans (tensorRepresentation b).symm) := by
  exact framedIsom_right (compensatedFrame ℂ S0 F) (dualCompensatedFrame ℂ S0 H)
    (compensatedFrame ℂ S0 (F * FrameAction.tetrahedralGL a))
    (dualCompensatedFrame ℂ S0 (H * FrameAction.tetrahedralGL b))
    (sourceIdentification a F) (targetIdentification b H) (tensorRepresentation a) (tensorRepresentation b) x
    (compensatedFrame_right_gamma a F) (dualCompensatedFrame_right_gamma b H)

end M9.MovingGammaGraphCoordinates

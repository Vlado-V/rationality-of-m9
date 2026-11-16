module

public import M9.MovingDeterminantFrames
public import M9.PrimitiveBlockCoordinates

/-!
# Actual dual moving frames and connected graph coordinates

The second moving plane lies in the actual dual Q∨ via the actual trace
pairing. Its SL₃ transport is the original contragredient action. Normalized
Hom coordinates are preserved by the actual connected tensor transports.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
open scoped Classical TensorProduct Matrix

namespace M9.MovingDualDeterminantFrames
open Module MovingDeterminantFrames

section GenericHelpers
variable {K V W Z Y X : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z] [AddCommGroup Y] [Module K Y]
  [AddCommGroup X] [Module K X]

theorem determinantDualTransport_symm (e : V ≃ₗ[K] W) :
    determinantDualTransport e.symm = (determinantDualTransport e).symm := by
  apply LinearEquiv.ext
  intro φ
  apply LinearMap.ext
  intro z
  rfl

theorem tensorTransport_symm (e : V ≃ₗ[K] W) :
    tensorTransport e.symm = (tensorTransport e).symm := by
  unfold tensorTransport
  rw [determinantDualTransport_symm, TensorProduct.congr_symm]

theorem tensorTransport_conjugate_weighted (e : V ≃ₗ[K] W) (f : V ≃ₗ[K] Z)
    (g : Z ≃ₗ[K] Y) (d : Kˣ) :
    (tensorTransport e).symm.trans
        (((tensorTransport f).trans (unitScalarEquiv (V := Twisted K Z) d)).trans (tensorTransport g)) =
      (tensorTransport (e.symm.trans (f.trans g))).trans (unitScalarEquiv (V := Twisted K Y) d) := by
  apply LinearEquiv.ext
  intro x
  change tensorTransport g ((d : K) • tensorTransport f ((tensorTransport e).symm x)) =
    (d : K) • tensorTransport (e.symm.trans (f.trans g)) x
  rw [map_smul, ← tensorTransport_symm, tensorTransport_trans, tensorTransport_trans]
  rfl

theorem extendFrame_connected (p : X ≃ₗ[K] V) (q : X ≃ₗ[K] W) (u : V ≃ₗ[K] W)
    (a : V ≃ₗ[K] Z) (b : W ≃ₗ[K] Y) (hp : p.trans u = q) :
    (p.trans a).trans (a.symm.trans (u.trans b)) = q.trans b := by
  apply LinearEquiv.ext
  intro x
  have he := congrArg (fun ρ : X ≃ₗ[K] W => ρ x) hp
  simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using congrArg b he

theorem extendFrame_comparison (p : X ≃ₗ[K] Twisted K V) (q : X ≃ₗ[K] Twisted K W)
    (j : V ≃ₗ[K] W) (a : V ≃ₗ[K] Z) (b : W ≃ₗ[K] Y) (j' : Z ≃ₗ[K] Y)
    (hp : p.trans (tensorTransport j) = q) (ha : a.trans j' = j.trans b) :
    (p.trans (tensorTransport a)).trans (tensorTransport j') = q.trans (tensorTransport b) := by
  rw [LinearEquiv.trans_assoc, ← tensorTransport_trans, ha, tensorTransport_trans,
    ← LinearEquiv.trans_assoc, hp]

end GenericHelpers

section ActualDual
variable (K : Type*) [Field K] [CharZero K]

local instance symPlaneGroup (S : Submodule K (Q K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }
local instance dualPlaneGroup (S : Submodule K (Module.Dual K (Q K))) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

/-- The moving second plane is a literal subspace of the actual linear dual. -/
def dualMovingPlane (S : Submodule K (Q K)) (H : GL3 K) : Submodule K (Module.Dual K (Q K)) :=
  (movingPlane K S H).map (PrimitiveBlockCoordinates.symmetricDualEquiv K).toLinearMap

def tracePlaneFrame (S : Submodule K (Q K)) (H : GL3 K) :
    movingPlane K S H ≃ₗ[K] dualMovingPlane K S H :=
  Submodule.equivMapOfInjective (PrimitiveBlockCoordinates.symmetricDualEquiv K).toLinearMap
    (PrimitiveBlockCoordinates.symmetricDualEquiv K).injective (movingPlane K S H)

@[simp] theorem tracePlaneFrame_val (S : Submodule K (Q K)) (H : GL3 K) (q : movingPlane K S H) :
    (tracePlaneFrame K S H q).val = PrimitiveBlockCoordinates.symmetricDualEquiv K q.val := rfl

def dualPlaneEquivOfEq {S T : Submodule K (Module.Dual K (Q K))} (h : S = T) : S ≃ₗ[K] T where
  toFun q := ⟨q.val,h ▸ q.property⟩
  invFun q := ⟨q.val,h.symm ▸ q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dualMovingPlane_eq (S : Submodule K (Q K)) (F H : GL3 K)
    (h : movingPlane K S F = movingPlane K S H) : dualMovingPlane K S F = dualMovingPlane K S H :=
  congrArg (fun P : Submodule K (Q K) =>
    P.map (PrimitiveBlockCoordinates.symmetricDualEquiv K).toLinearMap) h

theorem tracePlaneFrame_natural (S : Submodule K (Q K)) (F H : GL3 K)
    (h : movingPlane K S F = movingPlane K S H) :
    (tracePlaneFrame K S F).trans (dualPlaneEquivOfEq K (dualMovingPlane_eq K S F H h)) =
      (planeEquivOfEq K h).trans (tracePlaneFrame K S H) := by
  apply LinearEquiv.ext
  intro q
  apply Subtype.ext
  rfl

/-- The actual second compensated frame, with target in Q∨. -/
def dualCompensatedFrame (S : Submodule K (Q K)) (H : GL3 K) :
    Twisted K S ≃ₗ[K] Twisted K (dualMovingPlane K S H) :=
  (compensatedFrame K S H).trans (tensorTransport (tracePlaneFrame K S H))

theorem dualCompensatedFrame_scalar (S : Submodule K (Q K)) (b : Basis (Fin 4) K S)
    (a : Kˣ) (H : GL3 K) :
    (dualCompensatedFrame K S (Matrix.GeneralLinearGroup.scalar (Fin 3) a * H)).trans
        (tensorTransport (dualPlaneEquivOfEq K
          (dualMovingPlane_eq K S _ H (movingPlane_scalar K S a H)))) =
      dualCompensatedFrame K S H := by
  exact extendFrame_comparison (compensatedFrame K S (Matrix.GeneralLinearGroup.scalar (Fin 3) a * H))
    (compensatedFrame K S H) (planeEquivOfEq K (movingPlane_scalar K S a H))
    (tracePlaneFrame K S _) (tracePlaneFrame K S H)
    (dualPlaneEquivOfEq K (dualMovingPlane_eq K S _ H (movingPlane_scalar K S a H)))
    (compensatedFrame_scalar K S b a H) (tracePlaneFrame_natural K S _ H (movingPlane_scalar K S a H))

theorem dualCompensatedFrame_right (S : Submodule K (Q K)) (a H : GL3 K)
    (ha : movingPlane K S a = S) (hd : Matrix.GeneralLinearGroup.det a = 1) :
    (dualCompensatedFrame K S (H*a)).trans
        (tensorTransport (dualPlaneEquivOfEq K
          (dualMovingPlane_eq K S (H*a) H (movingPlane_right K S a H ha)))) =
      (tensorTransport (stabilizerAction K S a ha)).trans (dualCompensatedFrame K S H) := by
  have ht := extendFrame_comparison (compensatedFrame K S (H*a))
    ((tensorTransport (stabilizerAction K S a ha)).trans (compensatedFrame K S H))
    (planeEquivOfEq K (movingPlane_right K S a H ha))
    (tracePlaneFrame K S (H*a)) (tracePlaneFrame K S H)
    (dualPlaneEquivOfEq K (dualMovingPlane_eq K S (H*a) H (movingPlane_right K S a H ha)))
    (compensatedFrame_right K S a H ha hd) (tracePlaneFrame_natural K S (H*a) H (movingPlane_right K S a H ha))
  exact ht

/-- Genuine actual-dual plane transport, conjugated by the actual trace pairing. -/
def dualConnectedPlaneTransport (S : Submodule K (Q K)) (g H : GL3 K) :
    dualMovingPlane K S H ≃ₗ[K] dualMovingPlane K S (FrameAction.contragredient g * H) :=
  (tracePlaneFrame K S H).symm.trans
    ((connectedPlaneTransport K S (FrameAction.contragredient g) H).trans
      (tracePlaneFrame K S (FrameAction.contragredient g * H)))

/-- The actual tensor transport with the negative determinant character on
its GL₃ extension, transported into the actual Q∨ bundle. -/
def dualConnectedTensorTransport (S : Submodule K (Q K)) (g H : GL3 K) :
    Twisted K (dualMovingPlane K S H) ≃ₗ[K]
      Twisted K (dualMovingPlane K S (FrameAction.contragredient g * H)) :=
  (tensorTransport (tracePlaneFrame K S H)).symm.trans
    ((connectedTensorTransport K S (FrameAction.contragredient g) H).trans
      (tensorTransport (tracePlaneFrame K S (FrameAction.contragredient g * H))))

omit [CharZero K] in
theorem det_contragredient (g : GL3 K) :
    Matrix.GeneralLinearGroup.det (FrameAction.contragredient g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  apply Units.ext
  change ((g⁻¹).val.transpose).det = _
  rw [Matrix.det_transpose]
  exact congrArg Units.val (map_inv Matrix.GeneralLinearGroup.det g)

theorem dualConnectedTensorTransport_weight (S : Submodule K (Q K)) (g H : GL3 K) :
    dualConnectedTensorTransport K S g H =
      (tensorTransport (dualConnectedPlaneTransport K S g H)).trans
        (unitScalarEquiv (V := Twisted K (dualMovingPlane K S (FrameAction.contragredient g * H)))
          (((Matrix.GeneralLinearGroup.det g)⁻¹)^2)) := by
  have ht := tensorTransport_conjugate_weighted (tracePlaneFrame K S H)
    (connectedPlaneTransport K S (FrameAction.contragredient g) H)
    (tracePlaneFrame K S (FrameAction.contragredient g * H))
    ((Matrix.GeneralLinearGroup.det (FrameAction.contragredient g))^2)
  simpa only [dualConnectedTensorTransport, connectedTensorTransport, dualConnectedPlaneTransport,
    det_contragredient] using ht

theorem dualCompensatedFrame_connected (S : Submodule K (Q K)) (g H : GL3 K) :
    (dualCompensatedFrame K S H).trans (dualConnectedTensorTransport K S g H) =
      dualCompensatedFrame K S (FrameAction.contragredient g * H) := by
  exact extendFrame_connected (compensatedFrame K S H)
    (compensatedFrame K S (FrameAction.contragredient g * H))
    (connectedTensorTransport K S (FrameAction.contragredient g) H)
    (tensorTransport (tracePlaneFrame K S H))
    (tensorTransport (tracePlaneFrame K S (FrameAction.contragredient g * H)))
    (compensatedFrame_connected K S (FrameAction.contragredient g) H)

/-- On original SL₃ elements the target plane map is literally the original
contragredient of symmetric-square congruence, not a replacement action. -/
theorem dualConnectedPlaneTransport_sl3_val (S : Submodule K (Q K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (H : GL3 K) (q : dualMovingPlane K S H) :
    (dualConnectedPlaneTransport K S (Matrix.SpecialLinearGroup.toGL g) H q).val =
      (PrimitiveRepresentation.congruence K (g⁻¹).val).dualMap q.val := by
  obtain ⟨v,rfl⟩ := (tracePlaneFrame K S H).surjective q
  simp only [dualConnectedPlaneTransport, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, tracePlaneFrame_val]
  change PrimitiveBlockCoordinates.symmetricDualEquiv K
    (connectedPlaneTransport K S (FrameAction.contragredient (Matrix.SpecialLinearGroup.toGL g)) H v).val = _
  rw [connectedPlaneTransport_val]
  change PrimitiveBlockCoordinates.traceDual K
    (PrimitiveRepresentation.congruence K
      ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val.transpose v.val) =
        (PrimitiveRepresentation.congruence K (g⁻¹).val).dualMap
          (PrimitiveBlockCoordinates.traceDual K v.val)
  rw [← map_inv Matrix.SpecialLinearGroup.toGL g]
  exact PrimitiveBlockCoordinates.traceDual_contragredient K g v.val

theorem dualConnectedTensorTransport_det_one (S : Submodule K (Q K)) (g H : GL3 K)
    (hg : Matrix.GeneralLinearGroup.det g = 1) :
    dualConnectedTensorTransport K S g H = tensorTransport (dualConnectedPlaneTransport K S g H) := by
  rw [dualConnectedTensorTransport_weight, hg, inv_one, one_pow]
  apply LinearEquiv.ext
  intro x
  exact one_smul K _

theorem dualConnectedTensorTransport_sl3 (S : Submodule K (Q K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (H : GL3 K) :
    dualConnectedTensorTransport K S (Matrix.SpecialLinearGroup.toGL g) H =
      tensorTransport (dualConnectedPlaneTransport K S (Matrix.SpecialLinearGroup.toGL g) H) := by
  apply dualConnectedTensorTransport_det_one
  apply Units.ext
  exact g.property

end ActualDual

section IsomHelpers
variable {K U U' E E' F F' : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']
  [AddCommGroup E] [Module K E] [AddCommGroup E'] [Module K E']
  [AddCommGroup F] [Module K F] [AddCommGroup F'] [Module K F']

theorem framedIsom_transport (p : U ≃ₗ[K] E) (q : U' ≃ₗ[K] F)
    (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F') (x : E ≃ₗ[K] F) :
    (p.trans u).trans ((u.symm.trans (x.trans v)).trans (q.trans v).symm) = p.trans (x.trans q.symm) := by
  apply LinearEquiv.ext
  intro z
  change q.symm (v.symm (v (x (u.symm (u (p z)))))) = q.symm (x (p z))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end IsomHelpers

section ActualHom
variable (K : Type*) [Field K] [CharZero K]

local instance symPlaneGroup' (S : Submodule K (Q K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }
local instance dualPlaneGroup' (S : Submodule K (Module.Dual K (Q K))) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

def normalizedIsomCoordinates (S T : Submodule K (Q K)) (F H : GL3 K)
    (x : Twisted K (movingPlane K S F) ≃ₗ[K] Twisted K (dualMovingPlane K T H)) :
    Twisted K S ≃ₗ[K] Twisted K T :=
  (compensatedFrame K S F).trans (x.trans (dualCompensatedFrame K T H).symm)

def connectedIsomTransport (S T : Submodule K (Q K)) (g F H : GL3 K)
    (x : Twisted K (movingPlane K S F) ≃ₗ[K] Twisted K (dualMovingPlane K T H)) :
    Twisted K (movingPlane K S (g*F)) ≃ₗ[K]
      Twisted K (dualMovingPlane K T (FrameAction.contragredient g * H)) :=
  (connectedTensorTransport K S g F).symm.trans (x.trans (dualConnectedTensorTransport K T g H))

/-- Actual connected transport leaves the original normalized graph matrix
coordinates unchanged. This supplies the honest independent graph-coefficient
interpretation used by constant frame-field elimination. -/
theorem normalizedIsomCoordinates_connected (S T : Submodule K (Q K)) (g F H : GL3 K)
    (x : Twisted K (movingPlane K S F) ≃ₗ[K] Twisted K (dualMovingPlane K T H)) :
    normalizedIsomCoordinates K S T (g*F) (FrameAction.contragredient g * H)
        (connectedIsomTransport K S T g F H x) = normalizedIsomCoordinates K S T F H x := by
  have he := framedIsom_transport (compensatedFrame K S F) (dualCompensatedFrame K T H)
    (connectedTensorTransport K S g F) (dualConnectedTensorTransport K T g H) x
  simpa only [compensatedFrame_connected, dualCompensatedFrame_connected,
    normalizedIsomCoordinates, connectedIsomTransport] using he

end ActualHom

section ActualGamma
open StandardFourPlaneRepresentation TetrahedralGroup

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

theorem dualCompensatedFrame_right_gamma (g : Gamma) (H : GL3 ℂ) :
    (dualCompensatedFrame ℂ S0 (H * FrameAction.tetrahedralGL g)).trans
        (tensorTransport (dualPlaneEquivOfEq ℂ (dualMovingPlane_eq ℂ S0 _ H
          (movingPlane_right ℂ S0 (FrameAction.tetrahedralGL g) H (gammaPlane_eq g))))) =
      (tensorRepresentation g).trans (dualCompensatedFrame ℂ S0 H) := by
  have hd : Matrix.GeneralLinearGroup.det (FrameAction.tetrahedralGL g) = 1 := by
    apply Units.ext
    exact TetrahedralGroup.matrix_det g
  have ht := dualCompensatedFrame_right ℂ S0 (FrameAction.tetrahedralGL g) H (gammaPlane_eq g) hd
  rw [gammaTensorTransport_eq] at ht
  exact ht

end ActualGamma

end M9.MovingDualDeterminantFrames

module

public import M9.StandardFourPlaneRepresentation
public import M9.PrimitiveRepresentation
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Actual determinant-dual transport and moving projective frames

The determinant line is the actual dual of the fourth exterior power.
All frame transports are literal tensors of a linear equivalence with the
contragredient exterior-power equivalence.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open scoped Classical TensorProduct Matrix

namespace M9.MovingDeterminantFrames
open Module

abbrev DeterminantDual (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  Module.Dual K (⋀[K]^4 V)
abbrev Twisted (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  V ⊗[K] DeterminantDual K V

section Transport
variable {K V W Z : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

/-- Literal contragredient transport on the actual fourth exterior dual. -/
def determinantDualTransport (e : V ≃ₗ[K] W) : DeterminantDual K V ≃ₗ[K] DeterminantDual K W :=
  LinearEquiv.ofLinearMap (exteriorPower.map 4 e.symm.toLinearMap).dualMap
    (exteriorPower.map 4 e.toLinearMap).dualMap
    (by
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro z
      change φ (exteriorPower.map 4 e.toLinearMap (exteriorPower.map 4 e.symm.toLinearMap z)) = φ z
      have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; simp
      have hh : (exteriorPower.map 4 e.toLinearMap).comp (exteriorPower.map 4 e.symm.toLinearMap) =
          LinearMap.id := by rw [← exteriorPower.map_comp, he, exteriorPower.map_id]
      exact congrArg φ (LinearMap.congr_fun hh z))
    (by
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro z
      change φ (exteriorPower.map 4 e.symm.toLinearMap (exteriorPower.map 4 e.toLinearMap z)) = φ z
      have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
      have hh : (exteriorPower.map 4 e.symm.toLinearMap).comp (exteriorPower.map 4 e.toLinearMap) =
          LinearMap.id := by rw [← exteriorPower.map_comp, he, exteriorPower.map_id]
      exact congrArg φ (LinearMap.congr_fun hh z))

@[simp] theorem determinantDualTransport_apply (e : V ≃ₗ[K] W) (φ : DeterminantDual K V)
    (z : ⋀[K]^4 W) :
    determinantDualTransport e φ z = φ (exteriorPower.map 4 e.symm.toLinearMap z) := rfl

def tensorTransport (e : V ≃ₗ[K] W) : Twisted K V ≃ₗ[K] Twisted K W :=
  TensorProduct.congr e (determinantDualTransport e)

@[simp] theorem tensorTransport_tmul (e : V ≃ₗ[K] W) (v : V) (φ : DeterminantDual K V) :
    tensorTransport e (v ⊗ₜ[K] φ) = e v ⊗ₜ[K] determinantDualTransport e φ := rfl

theorem determinantDualTransport_trans (e : V ≃ₗ[K] W) (f : W ≃ₗ[K] Z) :
    determinantDualTransport (e.trans f) = (determinantDualTransport e).trans (determinantDualTransport f) := by
  apply LinearEquiv.ext
  intro φ
  apply LinearMap.ext
  intro z
  change φ (exteriorPower.map 4 (e.trans f).symm.toLinearMap z) =
    φ (exteriorPower.map 4 e.symm.toLinearMap (exteriorPower.map 4 f.symm.toLinearMap z))
  have he : (e.trans f).symm.toLinearMap = e.symm.toLinearMap.comp f.symm.toLinearMap := rfl
  rw [he, exteriorPower.map_comp]
  rfl

theorem tensorTransport_trans (e : V ≃ₗ[K] W) (f : W ≃ₗ[K] Z) :
    tensorTransport (e.trans f) = (tensorTransport e).trans (tensorTransport f) := by
  unfold tensorTransport
  rw [determinantDualTransport_trans]
  exact TensorProduct.congr_trans f (determinantDualTransport f) e (determinantDualTransport e)

/-- Coordinates on the actual dual determinant line, evaluated on an actual basis volume. -/
def determinantDualCoordinates (b : Basis (Fin 4) K V) : DeterminantDual K V ≃ₗ[K] K :=
  (exteriorPower.alternatingMapLinearEquiv (R := K) (n := 4) (M := V) (N := K)).symm.trans
    { toFun φ := φ b
      invFun c := c • b.det
      left_inv φ := (φ.eq_smul_basis_det b).symm
      right_inv c := by simp [Basis.det_self]
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

@[simp] theorem determinantDualCoordinates_apply (b : Basis (Fin 4) K V) (φ : DeterminantDual K V) :
    determinantDualCoordinates b φ = φ (exteriorPower.ιMulti K 4 b) :=
  exteriorPower.alternatingMapLinearEquiv_symm_apply φ b

def tensorTrivialization (b : Basis (Fin 4) K V) : Twisted K V ≃ₗ[K] V :=
  (TensorProduct.congr (LinearEquiv.refl K V) (determinantDualCoordinates b)).trans (TensorProduct.rid K V)

@[simp] theorem tensorTrivialization_tmul (b : Basis (Fin 4) K V) (v : V) (φ : DeterminantDual K V) :
    tensorTrivialization b (v ⊗ₜ[K] φ) = determinantDualCoordinates b φ • v := rfl

/-- The dual exterior transport has the actual inverse determinant character. -/
theorem determinantDualTransport_coordinates (b : Basis (Fin 4) K V) (e : V ≃ₗ[K] V)
    (φ : DeterminantDual K V) :
    determinantDualCoordinates b (determinantDualTransport e φ) =
      ((LinearEquiv.det e)⁻¹ : Kˣ).val * determinantDualCoordinates b φ := by
  let a : V [⋀^Fin 4]→ₗ[K] K := exteriorPower.alternatingMapLinearEquiv.symm φ
  have ha := congrArg (fun z : V [⋀^Fin 4]→ₗ[K] K => z (e.symm.toLinearMap ∘ b))
    (a.eq_smul_basis_det b)
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_comp,
    Basis.det_self, mul_one, ← LinearEquiv.coe_inv_det] at ha
  rw [determinantDualCoordinates_apply, determinantDualCoordinates_apply,
    determinantDualTransport_apply, exteriorPower.map_apply_ιMulti]
  change a (e.symm.toLinearMap ∘ b) = ((LinearEquiv.det e)⁻¹ : Kˣ).val * a b
  simpa only [mul_comm] using ha

theorem tensorTransport_trivialization (b : Basis (Fin 4) K V) (e : V ≃ₗ[K] V) (x : Twisted K V) :
    tensorTrivialization b (tensorTransport e x) =
      ((LinearEquiv.det e)⁻¹ : Kˣ).val • e (tensorTrivialization b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v φ =>
    rw [tensorTransport_tmul, tensorTrivialization_tmul, tensorTrivialization_tmul,
      determinantDualTransport_coordinates, map_smul, smul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]

theorem det_smulOfUnit_four (b : Basis (Fin 4) K V) (c : Kˣ) :
    LinearEquiv.det (LinearEquiv.smulOfUnit (M := V) c) = c^4 := by
  have hd : finrank K V = 4 := by rw [(b.equivFun).finrank_eq]; simp
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det ((c : K) • (LinearMap.id : V →ₗ[K] V)) = (c : K)^4
  rw [LinearMap.det_smul, hd, LinearMap.det_id, mul_one]

/-- The scalar weight of the actual tensor V ⊗ (⋀⁴V)∨ is c⁻³. -/
theorem tensorTransport_smulOfUnit (b : Basis (Fin 4) K V) (c : Kˣ) (x : Twisted K V) :
    tensorTransport (LinearEquiv.smulOfUnit (M := V) c) x = ((c⁻¹)^3 : Kˣ).val • x := by
  apply (tensorTrivialization b).injective
  rw [tensorTransport_trivialization, det_smulOfUnit_four b c, map_smul]
  change ((c^4)⁻¹ : Kˣ).val • ((c : K) • tensorTrivialization b x) = _
  rw [smul_smul, ← Units.val_mul]
  have hc : (c^4)⁻¹*c = (c⁻¹)^3 := by group
  rw [hc]

def unitScalarEquiv (c : Kˣ) : V ≃ₗ[K] V := LinearEquiv.smulOfUnit c

theorem tensorTransport_unitScalarEquiv (b : Basis (Fin 4) K V) (c : Kˣ) (x : Twisted K V) :
    tensorTransport (unitScalarEquiv (V := V) c) x = ((c⁻¹)^3 : Kˣ).val • x :=
  tensorTransport_smulOfUnit b c x

theorem weightedTransport_comparison (b : Basis (Fin 4) K V)
    (e : V ≃ₗ[K] W) (e' : V ≃ₗ[K] Z) (j : Z ≃ₗ[K] W) (c d d' : Kˣ)
    (he : e'.trans j = (unitScalarEquiv (V := V) c).trans e)
    (hd : d' * (c⁻¹)^3 = d) :
    ((tensorTransport e').trans (unitScalarEquiv (V := Twisted K Z) d')).trans (tensorTransport j) =
      (tensorTransport e).trans (unitScalarEquiv (V := Twisted K W) d) := by
  apply LinearEquiv.ext
  intro x
  have ht : tensorTransport j (tensorTransport e' x) =
      tensorTransport e (tensorTransport (unitScalarEquiv (V := V) c) x) := by
    change ((tensorTransport e').trans (tensorTransport j)) x =
      ((tensorTransport (unitScalarEquiv (V := V) c)).trans (tensorTransport e)) x
    rw [← tensorTransport_trans, he, tensorTransport_trans]
  change tensorTransport j ((d' : K) • tensorTransport e' x) = (d : K) • tensorTransport e x
  rw [map_smul, ht, tensorTransport_unitScalarEquiv b c, map_smul, smul_smul, ← Units.val_mul, hd]

theorem weightedTransport_natural (e : V ≃ₗ[K] W) (e' : V ≃ₗ[K] Z)
    (j : Z ≃ₗ[K] W) (r : V ≃ₗ[K] V) (d : Kˣ) (he : e'.trans j = r.trans e) :
    ((tensorTransport e').trans (unitScalarEquiv (V := Twisted K Z) d)).trans (tensorTransport j) =
      (tensorTransport r).trans ((tensorTransport e).trans (unitScalarEquiv (V := Twisted K W) d)) := by
  apply LinearEquiv.ext
  intro x
  have ht : tensorTransport j (tensorTransport e' x) = tensorTransport e (tensorTransport r x) := by
    change ((tensorTransport e').trans (tensorTransport j)) x =
      ((tensorTransport r).trans (tensorTransport e)) x
    rw [← tensorTransport_trans, he, tensorTransport_trans]
  change tensorTransport j ((d : K) • tensorTransport e' x) = (d : K) • tensorTransport e (tensorTransport r x)
  rw [map_smul, ht]

theorem weightedTransport_trans (e : V ≃ₗ[K] W) (f : W ≃ₗ[K] Z) (a b : Kˣ) :
    ((tensorTransport e).trans (unitScalarEquiv (V := Twisted K W) a)).trans
        ((tensorTransport f).trans (unitScalarEquiv (V := Twisted K Z) b)) =
      (tensorTransport (e.trans f)).trans (unitScalarEquiv (V := Twisted K Z) (b*a)) := by
  apply LinearEquiv.ext
  intro x
  change (b : K) • tensorTransport f ((a : K) • tensorTransport e x) =
    ((b*a : Kˣ).val) • tensorTransport (e.trans f) x
  rw [map_smul, smul_smul, ← Units.val_mul, tensorTransport_trans]
  rfl

end Transport


section MovingPlanes
variable (K : Type*) [Field K]

abbrev Q := M9.Symmetric3 K
abbrev GL3 := FrameAction.GL3 K

local instance planeAddCommGroup (S : Submodule K (Q K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

def congruenceEquiv (F : GL3 K) : Q K ≃ₗ[K] Q K :=
  LinearEquiv.ofLinearMap (PrimitiveRepresentation.congruence K F.val)
    (PrimitiveRepresentation.congruence K (F⁻¹).val)
    (by
      apply LinearMap.ext
      intro q
      change PrimitiveRepresentation.congruence K F.val
        (PrimitiveRepresentation.congruence K (F⁻¹).val q) = q
      rw [← PrimitiveRepresentation.congruence_mul, Units.mul_inv, PrimitiveRepresentation.congruence_one])
    (by
      apply LinearMap.ext
      intro q
      change PrimitiveRepresentation.congruence K (F⁻¹).val
        (PrimitiveRepresentation.congruence K F.val q) = q
      rw [← PrimitiveRepresentation.congruence_mul, Units.inv_mul, PrimitiveRepresentation.congruence_one])

theorem congruenceEquiv_mul (F G : GL3 K) (q : Q K) :
    congruenceEquiv K (F*G) q = congruenceEquiv K F (congruenceEquiv K G q) :=
  PrimitiveRepresentation.congruence_mul K F.val G.val q

theorem congruenceEquiv_scalar (a : Kˣ) (q : Q K) :
    congruenceEquiv K (Matrix.GeneralLinearGroup.scalar (Fin 3) a) q = (a^2 : Kˣ).val • q := by
  change PrimitiveRepresentation.congruence K (Matrix.scalar (Fin 3) (a : K)) q = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  simpa only [Units.val_pow_eq_pow_val] using PrimitiveRepresentation.congruence_scalar K (a : K) q

theorem congruenceEquiv_scalar_mul (a : Kˣ) (F : GL3 K) (q : Q K) :
    congruenceEquiv K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) q =
      (a^2 : Kˣ).val • congruenceEquiv K F q := by
  rw [congruenceEquiv_mul, congruenceEquiv_scalar]

def movingPlane (S : Submodule K (Q K)) (F : GL3 K) : Submodule K (Q K) :=
  S.map (congruenceEquiv K F).toLinearMap

def movingFrame (S : Submodule K (Q K)) (F : GL3 K) : S ≃ₗ[K] movingPlane K S F :=
  Submodule.equivMapOfInjective (congruenceEquiv K F).toLinearMap (congruenceEquiv K F).injective S

@[simp] theorem movingFrame_val (S : Submodule K (Q K)) (F : GL3 K) (q : S) :
    (movingFrame K S F q).val = congruenceEquiv K F q.val := rfl

def planeEquivOfEq {S T : Submodule K (Q K)} (h : S = T) : S ≃ₗ[K] T where
  toFun q := ⟨q.val,h ▸ q.property⟩
  invFun q := ⟨q.val,h.symm ▸ q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem planeEquivOfEq_val {S T : Submodule K (Q K)} (h : S = T) (q : S) :
    (planeEquivOfEq K h q).val = q.val := rfl

theorem movingPlane_scalar (S : Submodule K (Q K)) (a : Kˣ) (F : GL3 K) :
    movingPlane K S (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) = movingPlane K S F := by
  ext q
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨(a^2 : Kˣ).val • v, S.smul_mem _ hv, ?_⟩
    change congruenceEquiv K F ((a^2 : Kˣ).val • v) =
      congruenceEquiv K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) v
    rw [map_smul]
    exact (congruenceEquiv_scalar_mul K a F v).symm
  · rintro ⟨v,hv,rfl⟩
    refine ⟨((a^2)⁻¹ : Kˣ).val • v, S.smul_mem _ hv, ?_⟩
    change congruenceEquiv K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F)
      (((a^2)⁻¹ : Kˣ).val • v) = _
    rw [congruenceEquiv_scalar_mul, map_smul, smul_smul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_smul]
    rfl

theorem movingFrame_scalar (S : Submodule K (Q K)) (a : Kˣ) (F : GL3 K) :
    (movingFrame K S (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F)).trans
        (planeEquivOfEq K (movingPlane_scalar K S a F)) =
      (unitScalarEquiv (V := S) (a^2)).trans (movingFrame K S F) := by
  apply LinearEquiv.ext
  intro q
  apply Subtype.ext
  change congruenceEquiv K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) q.val =
    congruenceEquiv K F ((a^2 : Kˣ).val • q.val)
  rw [congruenceEquiv_scalar_mul, map_smul]

/-- The genuine determinant-compensated frame, with actual exterior-dual
transport and the manuscript's square determinant compensator. -/
def compensatedFrame (S : Submodule K (Q K)) (F : GL3 K) :
    Twisted K S ≃ₗ[K] Twisted K (movingPlane K S F) :=
  (tensorTransport (movingFrame K S F)).trans
    (unitScalarEquiv (V := Twisted K (movingPlane K S F))
      ((Matrix.GeneralLinearGroup.det F)^2))

theorem compensatedFrame_scalar (S : Submodule K (Q K)) (b : Basis (Fin 4) K S)
    (a : Kˣ) (F : GL3 K) :
    (compensatedFrame K S (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F)).trans
        (tensorTransport (planeEquivOfEq K (movingPlane_scalar K S a F))) =
      compensatedFrame K S F := by
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) =
      a^3 * Matrix.GeneralLinearGroup.det F := by
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar]
    rfl
  have hu : (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F))^2 *
      (((a^2)⁻¹)^3) = (Matrix.GeneralLinearGroup.det F)^2 := by
    rw [hd, mul_pow]
    have hc : (a^3)^2 * ((a^2)⁻¹)^3 = 1 := by group
    rw [mul_assoc, mul_comm ((Matrix.GeneralLinearGroup.det F)^2) (((a^2)⁻¹)^3),
      ← mul_assoc, hc, one_mul]
  exact weightedTransport_comparison b (movingFrame K S F)
    (movingFrame K S (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F))
    (planeEquivOfEq K (movingPlane_scalar K S a F)) (a^2) _ _ (movingFrame_scalar K S a F) hu

/-- Actual restriction of a stabilizing congruence to the original plane. -/
def stabilizerAction (S : Submodule K (Q K)) (a : GL3 K) (ha : movingPlane K S a = S) : S ≃ₗ[K] S :=
  (movingFrame K S a).trans (planeEquivOfEq K ha)

theorem movingPlane_right (S : Submodule K (Q K)) (a F : GL3 K) (ha : movingPlane K S a = S) :
    movingPlane K S (F*a) = movingPlane K S F := by
  ext q
  constructor
  · rintro ⟨v,hv,rfl⟩
    have hv' : congruenceEquiv K a v ∈ movingPlane K S a := ⟨v,hv,rfl⟩
    rw [ha] at hv'
    refine ⟨congruenceEquiv K a v,hv',?_⟩
    change congruenceEquiv K F (congruenceEquiv K a v) = congruenceEquiv K (F*a) v
    exact (congruenceEquiv_mul K F a v).symm
  · rintro ⟨v,hv,rfl⟩
    have hv' : v ∈ movingPlane K S a := ha.symm ▸ hv
    obtain ⟨w,hw,he⟩ := hv'
    refine ⟨w,hw,?_⟩
    change congruenceEquiv K (F*a) w = congruenceEquiv K F v
    rw [congruenceEquiv_mul]
    exact congrArg (congruenceEquiv K F) he

theorem movingFrame_right (S : Submodule K (Q K)) (a F : GL3 K) (ha : movingPlane K S a = S) :
    (movingFrame K S (F*a)).trans (planeEquivOfEq K (movingPlane_right K S a F ha)) =
      (stabilizerAction K S a ha).trans (movingFrame K S F) := by
  apply LinearEquiv.ext
  intro q
  apply Subtype.ext
  change congruenceEquiv K (F*a) q.val = congruenceEquiv K F (congruenceEquiv K a q.val)
  exact congruenceEquiv_mul K F a q.val

theorem compensatedFrame_right (S : Submodule K (Q K)) (a F : GL3 K)
    (ha : movingPlane K S a = S) (hd : Matrix.GeneralLinearGroup.det a = 1) :
    (compensatedFrame K S (F*a)).trans
        (tensorTransport (planeEquivOfEq K (movingPlane_right K S a F ha))) =
      (tensorTransport (stabilizerAction K S a ha)).trans (compensatedFrame K S F) := by
  have hdet : Matrix.GeneralLinearGroup.det (F*a) = Matrix.GeneralLinearGroup.det F := by
    rw [map_mul, hd, mul_one]
  have ht := weightedTransport_natural (movingFrame K S F) (movingFrame K S (F*a))
    (planeEquivOfEq K (movingPlane_right K S a F ha)) (stabilizerAction K S a ha)
    ((Matrix.GeneralLinearGroup.det F)^2) (movingFrame_right K S a F ha)
  simpa only [compensatedFrame, hdet] using ht

/-- The genuine restriction of the ambient connected congruence between
its two moving planes. -/
def connectedPlaneTransport (S : Submodule K (Q K)) (g F : GL3 K) :
    movingPlane K S F ≃ₗ[K] movingPlane K S (g*F) :=
  (movingFrame K S F).symm.trans (movingFrame K S (g*F))

theorem connectedPlaneTransport_val (S : Submodule K (Q K)) (g F : GL3 K)
    (q : movingPlane K S F) :
    (connectedPlaneTransport K S g F q).val = congruenceEquiv K g q.val := by
  obtain ⟨v,rfl⟩ := (movingFrame K S F).surjective q
  change congruenceEquiv K (g*F) ((movingFrame K S F).symm (movingFrame K S F v)).val = _
  rw [LinearEquiv.symm_apply_apply]
  exact congruenceEquiv_mul K g F v.val

theorem movingFrame_connected (S : Submodule K (Q K)) (g F : GL3 K) :
    (movingFrame K S F).trans (connectedPlaneTransport K S g F) = movingFrame K S (g*F) := by
  apply LinearEquiv.ext
  intro q
  simp only [connectedPlaneTransport, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The GL₃ extension multiplies actual tensor transport by det(g)²;
its restriction to SL₃ is the original actual tensor action. -/
def connectedTensorTransport (S : Submodule K (Q K)) (g F : GL3 K) :
    Twisted K (movingPlane K S F) ≃ₗ[K] Twisted K (movingPlane K S (g*F)) :=
  (tensorTransport (connectedPlaneTransport K S g F)).trans
    (unitScalarEquiv (V := Twisted K (movingPlane K S (g*F))) ((Matrix.GeneralLinearGroup.det g)^2))

theorem compensatedFrame_connected (S : Submodule K (Q K)) (g F : GL3 K) :
    (compensatedFrame K S F).trans (connectedTensorTransport K S g F) =
      compensatedFrame K S (g*F) := by
  have ht := weightedTransport_trans (movingFrame K S F) (connectedPlaneTransport K S g F)
    ((Matrix.GeneralLinearGroup.det F)^2) ((Matrix.GeneralLinearGroup.det g)^2)
  simpa only [compensatedFrame, connectedTensorTransport, movingFrame_connected, map_mul, mul_pow] using ht

theorem connectedTensorTransport_det_one (S : Submodule K (Q K)) (g F : GL3 K)
    (hg : Matrix.GeneralLinearGroup.det g = 1) :
    connectedTensorTransport K S g F = tensorTransport (connectedPlaneTransport K S g F) := by
  apply LinearEquiv.ext
  intro x
  change (((Matrix.GeneralLinearGroup.det g)^2 : Kˣ).val) •
    tensorTransport (connectedPlaneTransport K S g F) x = _
  rw [hg, one_pow, Units.val_one, one_smul]

end MovingPlanes

section ActualGamma
open StandardFourPlaneRepresentation TetrahedralGroup

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

theorem gammaPlane_eq (g : Gamma) : movingPlane ℂ S0 (FrameAction.tetrahedralGL g) = S0 := by
  ext q
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (gammaAction g ⟨v,hv⟩).property
  · intro hq
    let v := (gammaActionEquiv g).symm ⟨q,hq⟩
    refine ⟨v.val,v.property,?_⟩
    exact congrArg Subtype.val ((gammaActionEquiv g).apply_symm_apply ⟨q,hq⟩)

theorem gammaStabilizer_eq (g : Gamma) :
    stabilizerAction ℂ S0 (FrameAction.tetrahedralGL g) (gammaPlane_eq g) = gammaActionEquiv g := by
  apply LinearEquiv.ext
  intro q
  apply Subtype.ext
  rfl

theorem gammaTensorTransport_eq (g : Gamma) :
    tensorTransport (stabilizerAction ℂ S0 (FrameAction.tetrahedralGL g) (gammaPlane_eq g)) =
      tensorRepresentation g := by
  rw [gammaStabilizer_eq]
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q φ => rfl
  | add x y hx hy =>
    calc
      tensorTransport (gammaActionEquiv g) (x+y) =
          tensorTransport (gammaActionEquiv g) x + tensorTransport (gammaActionEquiv g) y :=
        (tensorTransport (gammaActionEquiv g)).map_add x y
      _ = tensorRepresentation g x + tensorRepresentation g y := congrArg₂ (· + ·) hx hy
      _ = tensorRepresentation g (x+y) := ((tensorRepresentation g).map_add x y).symm

theorem compensatedFrame_right_gamma (g : Gamma) (F : GL3 ℂ) :
    (compensatedFrame ℂ S0 (F * FrameAction.tetrahedralGL g)).trans
        (tensorTransport (planeEquivOfEq ℂ (movingPlane_right ℂ S0 (FrameAction.tetrahedralGL g) F
          (gammaPlane_eq g)))) =
      (tensorRepresentation g).trans (compensatedFrame ℂ S0 F) := by
  have hd : Matrix.GeneralLinearGroup.det (FrameAction.tetrahedralGL g) = 1 := by
    apply Units.ext
    exact TetrahedralGroup.matrix_det g
  have ht := compensatedFrame_right ℂ S0 (FrameAction.tetrahedralGL g) F (gammaPlane_eq g) hd
  rw [gammaTensorTransport_eq] at ht
  exact ht

end ActualGamma

end M9.MovingDeterminantFrames

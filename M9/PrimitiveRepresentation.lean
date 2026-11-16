module

public import M9.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Tactic.Ring

/-!
# The concrete primitive coordinate model

This module proves properties of the actual coordinate space
`K × Symmetric3 K × Symmetric3 K × K` and its displayed alternating form.
It does not identify this space with the kernel of contraction on `⋀³ K⁶`,
and it does not assert the Mukai or invariant-function-field bridge.
-/

@[expose] public section
noncomputable section

namespace M9.PrimitiveRepresentation

open Module
variable (K : Type*) [Field K]

/-- The concrete fourteen-dimensional coordinate space in Section 2. -/
abbrev Coordinates := K × (Symmetric3 K × (Symmetric3 K × K))

/-- The literal trace pairing on the two actual symmetric-matrix spaces. -/
def tracePair (X Y : Symmetric3 K) : K := Matrix.trace (X.val * Y.val)

@[simp] theorem tracePair_zero_left (Y : Symmetric3 K) : tracePair K 0 Y = 0 := by
  simp [tracePair]

@[simp] theorem tracePair_zero_right (X : Symmetric3 K) : tracePair K X 0 = 0 := by
  simp [tracePair]

theorem tracePair_comm (X Y : Symmetric3 K) : tracePair K X Y = tracePair K Y X :=
  Matrix.trace_mul_comm _ _

/-- A symmetric test matrix, with the diagonal counted twice. -/
def symmetricTest (i j : Fin 3) : Symmetric3 K :=
  ⟨Matrix.single i j 1 + Matrix.single j i 1, by
    change (Matrix.single i j (1 : K) + Matrix.single j i 1).transpose =
      Matrix.single i j 1 + Matrix.single j i 1
    simp only [Matrix.transpose_add, Matrix.transpose_single]
    exact add_comm _ _⟩

theorem tracePair_symmetricTest (X : Symmetric3 K) (i j : Fin 3) :
    tracePair K X (symmetricTest K i j) = 2 * X.val i j := by
  have hX : X.val j i = X.val i j := congrFun (congrFun X.property i) j
  simp [tracePair, symmetricTest, Matrix.mul_add, Matrix.trace_mul_single, hX, two_mul]

/-- The trace pairing on symmetric matrices is separating in characteristic zero. -/
theorem tracePair_separating [CharZero K] (X : Symmetric3 K)
    (hX : ∀ Y : Symmetric3 K, tracePair K X Y = 0) : X = 0 := by
  apply Subtype.ext
  funext i j
  have h := hX (symmetricTest K i j)
  rw [tracePair_symmetricTest] at h
  exact (mul_eq_zero.mp h).resolve_left (two_ne_zero : (2 : K) ≠ 0)

/-- The scalar formula used throughout the concrete coordinate model. -/
def pairingValue (r s : Coordinates K) : K :=
  r.1 * s.2.2.2 - s.1 * r.2.2.2 +
    tracePair K r.2.1 s.2.2.1 - tracePair K s.2.1 r.2.2.1

/-- The actual alternating bilinear form, with the manuscript's signs. -/
def pairing : LinearMap.BilinForm K (Coordinates K) where
  toFun r :=
    { toFun := pairingValue K r
      map_add' s t := by
        simp [pairingValue, tracePair, Matrix.mul_add, Matrix.add_mul]
        ring
      map_smul' c s := by
        simp [pairingValue, tracePair, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
        ring }
  map_add' r s := by
    apply LinearMap.ext
    intro t
    simp [pairingValue, tracePair, Matrix.mul_add, Matrix.add_mul]
    ring
  map_smul' c r := by
    apply LinearMap.ext
    intro s
    simp [pairingValue, tracePair, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
    ring

@[simp] theorem pairing_apply (r s : Coordinates K) :
    pairing K r s = r.1 * s.2.2.2 - s.1 * r.2.2.2 +
      Matrix.trace (r.2.1.val * s.2.2.1.val - s.2.1.val * r.2.2.1.val) := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, pairingValue, tracePair, Matrix.trace_sub]
  ring

@[simp] theorem pairing_isAlt : (pairing K).IsAlt := by
  intro r
  simp [pairing, pairingValue]

theorem pairing_neg_swap (r s : Coordinates K) : pairing K r s = -(pairing K s r) := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, pairingValue]
  ring

theorem pairing_separating_left [CharZero K] (r : Coordinates K)
    (hr : ∀ s : Coordinates K, pairing K r s = 0) : r = 0 := by
  rcases r with ⟨a, X, Y, b⟩
  have ha : a = 0 := by simpa [pairing, pairingValue] using hr (0, 0, 0, 1)
  have hb : b = 0 := by simpa [pairing, pairingValue] using hr (1, 0, 0, 0)
  have hX : X = 0 := tracePair_separating K X (fun Z => by
    simpa [pairing, pairingValue] using hr (0, 0, Z, 0))
  have hY : Y = 0 := tracePair_separating K Y (fun Z => by
    have h := hr (0, Z, 0, 0)
    simpa [pairing, pairingValue, tracePair_comm K Z Y] using h)
  simp [ha, hb, hX, hY]

theorem pairing_nondegenerate [CharZero K] : (pairing K).Nondegenerate := by
  constructor
  · exact pairing_separating_left K
  · intro r hr
    apply pairing_separating_left K r
    intro s
    rw [pairing_neg_swap, hr, neg_zero]

@[simp] theorem finrank_coordinates : finrank K (Coordinates K) = 14 := by
  simp [Coordinates, Module.finrank_prod]

/-- The twisted exchanging involution, including the scalar coordinate blocks. -/
def swap : Coordinates K ≃ₗ[K] Coordinates K where
  toFun r := (r.2.2.2, r.2.2.1, r.2.1, r.1)
  invFun r := (r.2.2.2, r.2.2.1, r.2.1, r.1)
  left_inv r := rfl
  right_inv r := rfl
  map_add' r s := rfl
  map_smul' c r := rfl

@[simp] theorem swap_apply (a b : K) (X Y : Symmetric3 K) :
    swap K (a,X,Y,b) = (b,Y,X,a) := rfl

@[simp] theorem swap_swap (r : Coordinates K) : swap K (swap K r) = r := rfl

/-- The twisted swap is anti-symplectic for the fixed scalar-valued form. -/
theorem swap_anti_pairing (r s : Coordinates K) :
    pairing K (swap K r) (swap K s) = -(pairing K r s) := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, pairingValue, swap,
    LinearEquiv.coe_mk]
  rw [tracePair_comm K r.2.2.1 s.2.1, tracePair_comm K s.2.2.1 r.2.1]
  ring

/-- Congruence on actual symmetric matrices. No determinant assumption is needed. -/
def congruence (g : Matrix (Fin 3) (Fin 3) K) : Symmetric3 K →ₗ[K] Symmetric3 K where
  toFun X := ⟨g * X.val * g.transpose, by
    change (g * X.val * g.transpose).transpose = g * X.val * g.transpose
    have hX : X.val.transpose = X.val := X.property
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hX, Matrix.mul_assoc]⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp] theorem congruence_val (g : Matrix (Fin 3) (Fin 3) K) (X : Symmetric3 K) :
    (congruence K g X).val = g * X.val * g.transpose := rfl

@[simp] theorem congruence_one (X : Symmetric3 K) : congruence K 1 X = X := by
  apply Subtype.ext
  simp

@[simp] theorem congruence_mul (g h : Matrix (Fin 3) (Fin 3) K) (X : Symmetric3 K) :
    congruence K (g*h) X = congruence K g (congruence K h X) := by
  apply Subtype.ext
  simp only [congruence_val, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The literal Section 2.3 action of `SL₃` on all four coordinate blocks. -/
def sl3Action (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Coordinates K →ₗ[K] Coordinates K :=
  LinearMap.prodMap LinearMap.id ((congruence K g.val).prodMap
    ((congruence K (g⁻¹).val.transpose).prodMap LinearMap.id))

@[simp] theorem sl3Action_apply (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (a b : K) (X Y : Symmetric3 K) :
    sl3Action K g (a,X,Y,b) =
      (a,congruence K g.val X,congruence K (g⁻¹).val.transpose Y,b) := rfl

@[simp] theorem sl3Action_one (r : Coordinates K) : sl3Action K 1 r = r := by
  rcases r with ⟨a,X,Y,b⟩
  simp

theorem sl3Action_mul (g h : Matrix.SpecialLinearGroup (Fin 3) K) (r : Coordinates K) :
    sl3Action K (g*h) r = sl3Action K g (sl3Action K h r) := by
  rcases r with ⟨a,X,Y,b⟩
  have hmul : (g*h).val = g.val*h.val := rfl
  have hinvmul : ((g*h)⁻¹).val = (h⁻¹).val*(g⁻¹).val := by rw [mul_inv_rev]; rfl
  simp only [sl3Action_apply, hmul, hinvmul, Matrix.transpose_mul, congruence_mul]

/-- A genuine linear representation, rather than a family of assumed actions. -/
def sl3Representation : Matrix.SpecialLinearGroup (Fin 3) K →* Module.End K (Coordinates K) where
  toFun := sl3Action K
  map_one' := by
    apply LinearMap.ext
    exact sl3Action_one K
  map_mul' g h := by
    apply LinearMap.ext
    exact sl3Action_mul K g h

theorem tracePair_sl3 (g : Matrix.SpecialLinearGroup (Fin 3) K) (X Y : Symmetric3 K) :
    tracePair K (congruence K g.val X) (congruence K (g⁻¹).val.transpose Y) =
      tracePair K X Y := by
  have hginvg : (g⁻¹).val * g.val = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  have ht : g.val.transpose * (g⁻¹).val.transpose = 1 := by
    rw [← Matrix.transpose_mul, hginvg, Matrix.transpose_one]
  change Matrix.trace ((g.val * X.val * g.val.transpose) *
    ((g⁻¹).val.transpose * Y.val * ((g⁻¹).val.transpose).transpose)) =
      Matrix.trace (X.val*Y.val)
  rw [Matrix.transpose_transpose]
  have hprod : (g.val * X.val * g.val.transpose) *
      ((g⁻¹).val.transpose * Y.val * (g⁻¹).val) =
      g.val * (X.val*Y.val) * (g⁻¹).val := by
    calc
      _ = g.val * X.val * (g.val.transpose*(g⁻¹).val.transpose) * Y.val * (g⁻¹).val := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [ht]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hprod, Matrix.trace_mul_cycle, hginvg, Matrix.one_mul]

/-- The actual connected coordinate action preserves the displayed form. -/
theorem sl3Action_pairing (g : Matrix.SpecialLinearGroup (Fin 3) K) (r s : Coordinates K) :
    pairing K (sl3Action K g r) (sl3Action K g s) = pairing K r s := by
  rcases r with ⟨a,X,Y,b⟩
  rcases s with ⟨a',X',Y',b'⟩
  change a*b'-a'*b+tracePair K (congruence K g.val X) (congruence K (g⁻¹).val.transpose Y') -
    tracePair K (congruence K g.val X') (congruence K (g⁻¹).val.transpose Y) = _
  rw [tracePair_sl3, tracePair_sl3]
  rfl

@[simp] theorem congruence_scalar (z : K) (X : Symmetric3 K) :
    congruence K (z • (1 : Matrix (Fin 3) (Fin 3) K)) X = z^2 • X := by
  apply Subtype.ext
  simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

/-- Every actual scalar element of `SL₃` has the stated two central characters. -/
theorem sl3Action_scalar (g : Matrix.SpecialLinearGroup (Fin 3) K) (z : K)
    (hg : g.val = z • (1 : Matrix (Fin 3) (Fin 3) K))
    (a b : K) (X Y : Symmetric3 K) :
    sl3Action K g (a,X,Y,b) = (a,z^2 • X,(z⁻¹)^2 • Y,b) := by
  have hz : z ≠ 0 := by
    intro hz
    have hdet : g.val.det = 1 := g.property
    rw [hg, hz, zero_smul] at hdet
    simpa using hdet
  have hginvg : (g⁻¹).val * g.val = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  have hzg : z • (g⁻¹).val = 1 := by
    simpa only [hg, Matrix.mul_smul, Matrix.mul_one] using hginvg
  have hgi : (g⁻¹).val = z⁻¹ • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => z⁻¹ • M) hzg
    simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using h
  rw [sl3Action_apply, hg, hgi]
  simp

/-- A cube root of unity gives a genuine central special-linear matrix. -/
def centralElement (z : K) (hz : z^3 = 1) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨z • (1 : Matrix (Fin 3) (Fin 3) K), by
    simp [Matrix.det_smul, hz]⟩

theorem centralElement_mem_center (z : K) (hz : z^3 = 1) :
    centralElement K z hz ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  change g.val * (z • (1 : Matrix (Fin 3) (Fin 3) K)) =
    (z • (1 : Matrix (Fin 3) (Fin 3) K)) * g.val
  simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem sl3Action_centralElement (z : K) (hz : z^3 = 1)
    (a b : K) (X Y : Symmetric3 K) :
    sl3Action K (centralElement K z hz) (a,X,Y,b) =
      (a,z^2 • X,(z⁻¹)^2 • Y,b) :=
  sl3Action_scalar K (centralElement K z hz) z rfl a b X Y

/-- Inverse transpose is the automorphism governing the exchanging component. -/
def inverseTranspose (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix.SpecialLinearGroup (Fin 3) K := (g⁻¹).transpose

@[simp] theorem inverseTranspose_val (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (inverseTranspose K g).val = (g⁻¹).val.transpose := rfl

theorem inverseTranspose_inv (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (inverseTranspose K g)⁻¹ = g.transpose := by
  have ht : inverseTranspose K g * g.transpose = 1 := by
    apply Subtype.ext
    change (g⁻¹).val.transpose * g.val.transpose = 1
    rw [← Matrix.transpose_mul]
    have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
    rw [h, Matrix.transpose_one]
  calc
    (inverseTranspose K g)⁻¹ = (inverseTranspose K g)⁻¹ * 1 := (mul_one _).symm
    _ = (inverseTranspose K g)⁻¹ * (inverseTranspose K g * g.transpose) := by rw [ht]
    _ = g.transpose := by rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- The literal swap conjugates the actual connected action by inverse transpose. -/
theorem swap_sl3Action (g : Matrix.SpecialLinearGroup (Fin 3) K) (r : Coordinates K) :
    swap K (sl3Action K g r) = sl3Action K (inverseTranspose K g) (swap K r) := by
  rcases r with ⟨a,X,Y,b⟩
  simp only [sl3Action_apply, swap_apply, inverseTranspose_val, inverseTranspose_inv]
  rfl

end M9.PrimitiveRepresentation

module

public import M9.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.FieldTheory.Fixed
public import Mathlib.Tactic

/-!
# Elimination of an actual constant general-linear frame

Over an infinite base field, invariance under all constant invertible frame
changes forces a rational function to belong to its coefficient field.
The proof chooses an actual invertible constant matrix avoiding the given
denominator. No infinite-group quotient or generic-invariance premise is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical Matrix BigOperators

namespace M9.ConstantFrameElimination

open MvPolynomial

abbrev Index (n : ℕ) := Fin n × Fin n
abbrev PolynomialRing (A : Type*) [Field A] (n : ℕ) := MvPolynomial (Index n) A
abbrev FunctionField (A : Type*) [Field A] (n : ℕ) := FractionRing (PolynomialRing A n)
abbrev GLn (K : Type*) [Field K] (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) K

variable (K A : Type*) [Field K] [Infinite K] [Field A] [Algebra K A] (n : ℕ)

def evaluateAt (M : Matrix (Fin n) (Fin n) K) : PolynomialRing A n →ₐ[A] A :=
  aeval (fun ij => algebraMap K A (M ij.1 ij.2))

omit [Infinite K] in
@[simp] theorem evaluateAt_C (M : Matrix (Fin n) (Fin n) K) (a : A) :
    evaluateAt K A n M (C a) = a := by simp [evaluateAt]

omit [Infinite K] in
@[simp] theorem evaluateAt_X (M : Matrix (Fin n) (Fin n) K) (ij : Index n) :
    evaluateAt K A n M (X ij) = algebraMap K A (M ij.1 ij.2) := by simp [evaluateAt]

/-- Constant matrices over the original infinite field detect polynomials,
even after extending the coefficient field. -/
theorem polynomial_ext_constants {p q : PolynomialRing A n}
    (h : ∀ M : Matrix (Fin n) (Fin n) K, evaluateAt K A n M p = evaluateAt K A n M q) :
    p = q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (algebraMap K A))
    (fun _ => Set.infinite_range_of_injective (algebraMap K A).injective)
  intro x hx
  choose v hv using (fun ij : Index n => hx ij (Set.mem_univ ij))
  have he : x = fun ij => algebraMap K A (v ij) := funext (fun ij => (hv ij).symm)
  rw [he]
  exact h (fun i j => v (i,j))

def genericMatrix : Matrix (Fin n) (Fin n) (PolynomialRing A n) := fun i j => X (i,j)
def determinantPolynomial : PolynomialRing A n := (genericMatrix A n).det

omit [Infinite K] in
theorem evaluateAt_determinant (M : Matrix (Fin n) (Fin n) K) :
    evaluateAt K A n M (determinantPolynomial A n) = algebraMap K A M.det := by
  have hm : (genericMatrix A n).map (evaluateAt K A n M).toRingHom = M.map (algebraMap K A) := by
    ext i j
    exact evaluateAt_X K A n M (i,j)
  rw [determinantPolynomial, AlgHom.map_det]
  change ((genericMatrix A n).map (evaluateAt K A n M).toRingHom).det = _
  rw [hm]
  exact ((algebraMap K A).map_det M).symm

theorem determinantPolynomial_ne_zero : determinantPolynomial A n ≠ 0 := by
  intro h
  have he := evaluateAt_determinant A A n (1 : Matrix (Fin n) (Fin n) A)
  rw [h, map_zero, Matrix.det_one, map_one] at he
  exact zero_ne_one he

/-- Density of the actual invertible constant matrices, proved by multiplying
by the literal universal determinant before polynomial extensionality. -/
theorem polynomial_eq_zero_of_invertible_constants (p : PolynomialRing A n)
    (h : ∀ g : GLn K n, evaluateAt K A n g.val p = 0) : p = 0 := by
  have hp : p * determinantPolynomial A n = 0 := by
    apply polynomial_ext_constants K A n
    intro M
    rw [map_mul, map_zero, evaluateAt_determinant]
    by_cases hM : M.det = 0
    · simp [hM]
    · let g : GLn K n := Matrix.GeneralLinearGroup.mkOfDetNeZero M hM
      have hg := h g
      change evaluateAt K A n M p = 0 at hg
      rw [hg, zero_mul]
  exact (mul_eq_zero.mp hp).resolve_right (determinantPolynomial_ne_zero A n)

theorem exists_invertible_constant_avoiding (p : PolynomialRing A n) (hp : p ≠ 0) :
    ∃ g : GLn K n, evaluateAt K A n g.val p ≠ 0 := by
  by_contra h
  apply hp
  exact polynomial_eq_zero_of_invertible_constants K A n p (by simpa using h)

/-- The literal pullback along left matrix multiplication. -/
def leftSubstitution (g : Matrix (Fin n) (Fin n) K) : PolynomialRing A n →ₐ[A] PolynomialRing A n :=
  aeval (fun ij => ∑ k : Fin n, C (algebraMap K A (g ij.1 k)) * X (k,ij.2))

omit [Infinite K] in
@[simp] theorem leftSubstitution_C (g : Matrix (Fin n) (Fin n) K) (a : A) :
    leftSubstitution K A n g (C a) = C a := by simp [leftSubstitution]

omit [Infinite K] in
@[simp] theorem leftSubstitution_X (g : Matrix (Fin n) (Fin n) K) (ij : Index n) :
    leftSubstitution K A n g (X ij) = ∑ k : Fin n, C (algebraMap K A (g ij.1 k)) * X (k,ij.2) := by
  simp [leftSubstitution]

omit [Infinite K] in
theorem evaluateAt_leftSubstitution (g M : Matrix (Fin n) (Fin n) K) (p : PolynomialRing A n) :
    evaluateAt K A n M (leftSubstitution K A n g p) = evaluateAt K A n (g*M) p := by
  have he : (evaluateAt K A n M).comp (leftSubstitution K A n g) = evaluateAt K A n (g*M) := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp [Matrix.mul_apply, map_sum, map_mul]
  exact AlgHom.congr_fun he p

theorem leftSubstitution_comp (g h : Matrix (Fin n) (Fin n) K) :
    (leftSubstitution K A n g).comp (leftSubstitution K A n h) = leftSubstitution K A n (h*g) := by
  apply AlgHom.ext
  intro p
  apply polynomial_ext_constants K A n
  intro M
  change evaluateAt K A n M (leftSubstitution K A n g (leftSubstitution K A n h p)) = _
  rw [evaluateAt_leftSubstitution, evaluateAt_leftSubstitution, evaluateAt_leftSubstitution]
  rw [Matrix.mul_assoc]

theorem leftSubstitution_one :
    leftSubstitution K A n 1 = AlgHom.id A (PolynomialRing A n) := by
  apply AlgHom.ext
  intro p
  apply polynomial_ext_constants K A n
  intro M
  simp only [evaluateAt_leftSubstitution, Matrix.one_mul, AlgHom.id_apply]

def leftPolynomialEquiv (g : GLn K n) : PolynomialRing A n ≃ₐ[A] PolynomialRing A n :=
  AlgEquiv.ofAlgHom (leftSubstitution K A n g.val) (leftSubstitution K A n (g⁻¹).val)
    (by rw [leftSubstitution_comp, Units.inv_mul, leftSubstitution_one])
    (by rw [leftSubstitution_comp, Units.mul_inv, leftSubstitution_one])

def leftFractionEquiv (g : GLn K n) : FunctionField A n ≃ₐ[A] FunctionField A n :=
  IsFractionRing.algEquivOfAlgEquiv (leftPolynomialEquiv K A n g)

theorem leftFractionEquiv_polynomial (g : GLn K n) (p : PolynomialRing A n) :
    leftFractionEquiv K A n g (algebraMap (PolynomialRing A n) (FunctionField A n) p) =
      algebraMap (PolynomialRing A n) (FunctionField A n) (leftSubstitution K A n g.val p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (leftPolynomialEquiv K A n g) p

/-- A rational invariant under every actual constant left frame change is a
constant in the supplied coefficient field. The denominator-avoiding point
is constructed, rather than assumed regular at the identity matrix. -/
theorem invariant_fraction_is_constant (f : FunctionField A n)
    (hf : ∀ g : GLn K n, leftFractionEquiv K A n g f = f) :
    ∃ a : A, algebraMap A (FunctionField A n) a = f := by
  let j := algebraMap (PolynomialRing A n) (FunctionField A n)
  have hj := IsFractionRing.injective (PolynomialRing A n) (FunctionField A n)
  obtain ⟨p,q,hq,rfl⟩ := IsFractionRing.div_surjective (PolynomialRing A n) f
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hjq : j q ≠ 0 := fun h => hq0 (hj (h.trans (map_zero j).symm))
  have hcross (g : GLn K n) : leftSubstitution K A n g.val p * q = p * leftSubstitution K A n g.val q := by
    have h := hf g
    rw [map_div₀, leftFractionEquiv_polynomial, leftFractionEquiv_polynomial] at h
    have hgq : j (leftSubstitution K A n g.val q) ≠ 0 := by
      intro hz
      have he : leftPolynomialEquiv K A n g q = leftPolynomialEquiv K A n g 0 := by
        apply hj
        exact hz.trans (map_zero j).symm
      exact hq0 ((leftPolynomialEquiv K A n g).injective he)
    apply hj
    simpa only [map_mul] using (div_eq_div_iff hgq hjq).mp h
  obtain ⟨c,hc⟩ := exists_invertible_constant_avoiding K A n q hq0
  have hpoly : p * C (evaluateAt K A n c.val q) - q * C (evaluateAt K A n c.val p) = 0 := by
    apply polynomial_eq_zero_of_invertible_constants K A n
    intro g
    have he := congrArg (evaluateAt K A n c.val) (hcross (g*c⁻¹))
    simp only [map_mul, evaluateAt_leftSubstitution] at he
    have hgc : (g*c⁻¹).val * c.val = g.val := by
      exact congrArg Units.val (by simp [mul_assoc] : (g*c⁻¹)*c = g)
    rw [hgc] at he
    simp only [map_sub, map_mul, evaluateAt_C]
    rw [he]
    ring
  refine ⟨evaluateAt K A n c.val p / evaluateAt K A n c.val q, ?_⟩
  rw [map_div₀]
  apply (div_eq_div_iff (by simpa only [map_zero] using
    (algebraMap A (FunctionField A n)).injective.ne hc) hjq).mpr
  have he := congrArg j hpoly
  simp only [map_sub, map_mul, map_zero] at he
  change j p * algebraMap A (FunctionField A n) (evaluateAt K A n c.val q) -
    j q * algebraMap A (FunctionField A n) (evaluateAt K A n c.val p) = 0 at he
  simpa only [mul_comm] using (sub_eq_zero.mp he).symm

theorem invariant_fraction_iff_constant (f : FunctionField A n) :
    (∀ g : GLn K n, leftFractionEquiv K A n g f = f) ↔
      ∃ a : A, algebraMap A (FunctionField A n) a = f := by
  constructor
  · exact invariant_fraction_is_constant K A n f
  · rintro ⟨a,rfl⟩ g
    exact (leftFractionEquiv K A n g).commutes a

/-- Invariance under all constant matrices implies invariance after any two
coefficient-preserving generic frame substitutions. -/
theorem invariant_fraction_hom_eq {L : Type*} [Field L] [Algebra A L]
    (f : FunctionField A n) (hf : ∀ g : GLn K n, leftFractionEquiv K A n g f = f)
    (φ ψ : FunctionField A n →ₐ[A] L) : φ f = ψ f := by
  obtain ⟨a,rfl⟩ := invariant_fraction_is_constant K A n f hf
  rw [φ.commutes, ψ.commutes]

theorem leftFractionEquiv_one : leftFractionEquiv K A n 1 = 1 := by
  have he : (leftFractionEquiv K A n 1).toRingHom = RingHom.id (FunctionField A n) := by
    apply IsFractionRing.ringHom_ext (A := PolynomialRing A n)
    intro p
    change leftFractionEquiv K A n 1 (algebraMap (PolynomialRing A n) (FunctionField A n) p) = _
    rw [leftFractionEquiv_polynomial]
    change algebraMap (PolynomialRing A n) (FunctionField A n) (leftSubstitution K A n 1 p) = _
    rw [leftSubstitution_one]
    rfl
  exact AlgEquiv.ext (fun f => RingHom.congr_fun he f)

theorem leftFractionEquiv_mul (g h : GLn K n) :
    leftFractionEquiv K A n (g*h) = leftFractionEquiv K A n h * leftFractionEquiv K A n g := by
  have he : (leftFractionEquiv K A n (g*h)).toRingHom =
      (leftFractionEquiv K A n h).toRingHom.comp (leftFractionEquiv K A n g).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := PolynomialRing A n)
    intro p
    change leftFractionEquiv K A n (g*h) (algebraMap (PolynomialRing A n) (FunctionField A n) p) =
      leftFractionEquiv K A n h
        (leftFractionEquiv K A n g (algebraMap (PolynomialRing A n) (FunctionField A n) p))
    rw [leftFractionEquiv_polynomial, leftFractionEquiv_polynomial, leftFractionEquiv_polynomial]
    change algebraMap (PolynomialRing A n) (FunctionField A n)
      (leftSubstitution K A n (g*h).val p) =
        algebraMap (PolynomialRing A n) (FunctionField A n)
          (((leftSubstitution K A n h.val).comp (leftSubstitution K A n g.val)) p)
    rw [leftSubstitution_comp]
    rfl
  exact AlgEquiv.ext (fun f => RingHom.congr_fun he f)

/-- The ordinary left group action uses inverse pullback on coordinates. -/
def leftActionHom : GLn K n →* (FunctionField A n ≃ₐ[A] FunctionField A n) where
  toFun g := leftFractionEquiv K A n g⁻¹
  map_one' := by rw [inv_one, leftFractionEquiv_one]
  map_mul' g h := by rw [mul_inv_rev, leftFractionEquiv_mul]

/-- The native fixed intermediate field of the actual infinite group of
constant changes of frame. -/
def nativeFixedField : IntermediateField A (FunctionField A n) :=
  IntermediateField.fixedField (leftActionHom K A n).range

theorem mem_nativeFixedField_iff (f : FunctionField A n) :
    f ∈ nativeFixedField K A n ↔ ∀ g : GLn K n, leftFractionEquiv K A n g f = f := by
  rw [nativeFixedField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h g
    have he := h (leftActionHom K A n g⁻¹) ⟨g⁻¹,rfl⟩
    simpa only [leftActionHom, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv] using he
  · intro h σ hσ
    obtain ⟨g,rfl⟩ := hσ
    exact h g⁻¹

theorem nativeFixedField_eq_bot : nativeFixedField K A n = ⊥ := by
  ext f
  rw [mem_nativeFixedField_iff, invariant_fraction_iff_constant, IntermediateField.mem_bot]
  rfl

/-- The fixed field is identified with the supplied coefficient field by
its actual coefficient inclusion. -/
def coefficientFixedEquiv : A ≃ₐ[A] nativeFixedField K A n :=
  AlgEquiv.ofBijective (Algebra.ofId A (nativeFixedField K A n))
    ⟨(Algebra.ofId A (nativeFixedField K A n)).injective, by
      intro f
      obtain ⟨a,ha⟩ := invariant_fraction_is_constant K A n f.val
        ((mem_nativeFixedField_iff K A n f.val).mp f.property)
      exact ⟨a,Subtype.ext ha⟩⟩

end M9.ConstantFrameElimination

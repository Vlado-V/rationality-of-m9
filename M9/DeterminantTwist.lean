module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

/-!
# The determinant twist in rank four

The actual matrix map is `X ↦ (det X)⁻¹ • X`. On invertible matrices its
fibers are exactly the scalar cube-root orbits, and it commutes with matrix
inversion. These pointwise statements do not assert an invariant-ring or
relative-scheme quotient.
-/

@[expose] public section

noncomputable section

namespace M9.DeterminantTwist

variable {K : Type*} [Field K]

abbrev Mat4 (K : Type*) := Matrix (Fin 4) (Fin 4) K

/-- The local matrix expression of the determinant twist in Proposition 3.1. -/
def twist (X : Mat4 K) : Mat4 K := X.det⁻¹ • X

theorem det_smul_four (X : Mat4 K) (a : K) : (a • X).det = a^4 * X.det := by
  simp

theorem det_twist (X : Mat4 K) (hX : X.det ≠ 0) :
    (twist X).det = (X.det⁻¹)^3 := by
  rw [twist, det_smul_four]
  field_simp

theorem det_twist_zpow (X : Mat4 K) (hX : X.det ≠ 0) :
    (twist X).det = X.det ^ (-3 : ℤ) := by
  rw [det_twist X hX]
  simp [zpow_neg, inv_pow]

theorem det_twist_ne_zero (X : Mat4 K) (hX : X.det ≠ 0) : (twist X).det ≠ 0 := by
  rw [det_twist X hX]
  exact pow_ne_zero _ (inv_ne_zero hX)

/-- The determinant of the original matrix recovers it from its twist. -/
theorem recover (X : Mat4 K) (hX : X.det ≠ 0) : X.det • twist X = X := by
  simp [twist, smul_smul, hX]

/-- The covering equation appearing in the coordinate-ring presentation. -/
theorem determinant_cover_equation (X : Mat4 K) (hX : X.det ≠ 0) :
    X.det^3 * (twist X).det = 1 := by
  rw [det_twist X hX]
  field_simp

theorem det_inverse (X : Mat4 K) : X⁻¹.det = X.det⁻¹ := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

theorem twist_inverse (X : Mat4 K) (hX : X.det ≠ 0) :
    twist X⁻¹ = (twist X)⁻¹ := by
  rw [twist, det_inverse, inv_inv]
  symm
  apply Matrix.inv_eq_right_inv
  rw [twist, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_nonsing_inv X (isUnit_iff_ne_zero.mpr hX), smul_smul]
  simp [hX]

theorem cubeRoot_ne_zero (a : K) (ha : a^3 = 1) : a ≠ 0 := by
  intro h
  simp [h] at ha

/-- The twist is invariant under the actual scalar cube-root action. -/
theorem twist_smul_cubeRoot (X : Mat4 K) (hX : X.det ≠ 0) (a : K) (ha : a^3 = 1) :
    twist (a • X) = twist X := by
  have ha0 := cubeRoot_ne_zero a ha
  have ha4 : a^4 = a := by
    calc
      a^4 = a^3 * a := by ring
      _ = a := by rw [ha, one_mul]
  rw [twist, det_smul_four, ha4, smul_smul, twist]
  congr 1
  field_simp

theorem det_smul_cubeRoot_ne_zero (X : Mat4 K) (hX : X.det ≠ 0)
    (a : K) (ha : a^3 = 1) : (a • X).det ≠ 0 := by
  rw [det_smul_four]
  exact mul_ne_zero (pow_ne_zero _ (cubeRoot_ne_zero a ha)) hX

/-- Over any field, two invertible matrices have the same twist precisely
when one is a scalar cube-root multiple of the other. -/
theorem twist_eq_iff (X Y : Mat4 K) (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    twist X = twist Y ↔ ∃ a : K, a^3 = 1 ∧ Y = a • X := by
  constructor
  · intro h
    let a := Y.det / X.det
    have ha0 : a ≠ 0 := div_ne_zero hY hX
    have hYX : Y = a • X := by
      have hs := congrArg (fun Z : Mat4 K => Y.det • Z) h
      simpa [twist, smul_smul, hY, div_eq_mul_inv, a] using hs.symm
    have hd : Y.det = a^4 * X.det := by simpa only [det_smul_four] using congrArg Matrix.det hYX
    have hr : Y.det = a * X.det := by
      dsimp [a]
      field_simp
    have ha4 : a^4 = a := by
      apply mul_right_cancel₀ hX
      exact hd.symm.trans hr
    refine ⟨a, ?_, hYX⟩
    apply mul_right_cancel₀ ha0
    simpa only [← pow_succ, one_mul] using ha4
  · rintro ⟨a, ha, rfl⟩
    exact (twist_smul_cubeRoot X hX a ha).symm

/-- The same exact fiber statement using Mathlib's actual subgroup `μ₃`. -/
theorem twist_eq_iff_rootsOfUnity (X Y : Mat4 K) (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    twist X = twist Y ↔ ∃ a : rootsOfUnity 3 K, Y = (a.val : K) • X := by
  rw [twist_eq_iff X Y hX hY]
  constructor
  · rintro ⟨a, ha, hYX⟩
    exact ⟨rootsOfUnity.mkOfPowEq a ha, by simpa using hYX⟩
  · rintro ⟨a, hYX⟩
    exact ⟨(a.val : K), (mem_rootsOfUnity' 3 a.val).mp a.property, hYX⟩

theorem twist_singular (X : Mat4 K) (hX : X.det = 0) : twist X = 0 := by
  simp [twist, hX]

theorem twist_eq_zero_iff (X : Mat4 K) : twist X = 0 ↔ X.det = 0 := by
  constructor
  · intro h
    by_contra hX
    have hn := det_twist_ne_zero X hX
    simp [h] at hn
  · exact twist_singular X

theorem twist_one : twist (1 : Mat4 K) = 1 := by simp [twist]

theorem twist_mul (X Y : Mat4 K) : twist (X * Y) = twist X * twist Y := by
  simp only [twist, Matrix.det_mul, mul_inv_rev, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

theorem scalar_central (a : K) (X : Mat4 K) :
    Matrix.scalar (Fin 4) a * X = X * Matrix.scalar (Fin 4) a :=
  Matrix.scalar_comm a (fun _ => Commute.all _ _) X

/-- The covering equation forces its determinant parameter to be nonzero. -/
theorem cover_scalar_ne_zero (Z : Mat4 K) (d : K) (hd : d^3 * Z.det = 1) : d ≠ 0 := by
  intro h
  simp [h] at hd

theorem cover_det_ne_zero (Z : Mat4 K) (d : K) (hd : d^3 * Z.det = 1) : Z.det ≠ 0 := by
  intro h
  simp [h] at hd

/-- Conversely, `X=dZ` has determinant exactly `d` under the covering equation. -/
theorem det_reconstruct (Z : Mat4 K) (d : K) (hd : d^3 * Z.det = 1) : (d • Z).det = d := by
  rw [det_smul_four]
  calc
    d^4 * Z.det = d * (d^3 * Z.det) := by ring
    _ = d := by rw [hd, mul_one]

theorem twist_reconstruct (Z : Mat4 K) (d : K) (hd : d^3 * Z.det = 1) :
    twist (d • Z) = Z := by
  rw [twist, det_reconstruct Z d hd, smul_smul,
    inv_mul_cancel₀ (cover_scalar_ne_zero Z d hd), one_smul]

/-- Exact pointwise solvability of the twist, over an arbitrary field. -/
theorem exists_twist_preimage_iff (Z : Mat4 K) :
    (∃ X : Mat4 K, X.det ≠ 0 ∧ twist X = Z) ↔ ∃ d : K, d^3 * Z.det = 1 := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X.det, determinant_cover_equation X hX⟩
  · rintro ⟨d, hd⟩
    exact ⟨d • Z, by rw [det_reconstruct Z d hd]; exact cover_scalar_ne_zero Z d hd,
      twist_reconstruct Z d hd⟩

theorem exists_twist_preimage [IsAlgClosed K] (Z : Mat4 K) (hZ : Z.det ≠ 0) :
    ∃ X : Mat4 K, X.det ≠ 0 ∧ twist X = Z := by
  apply (exists_twist_preimage_iff Z).mpr
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq Z.det⁻¹ (by norm_num : 0 < 3)
  exact ⟨d, by rw [hd, inv_mul_cancel₀ hZ]⟩

abbrev GL4 (K : Type*) [Field K] := Matrix.GeneralLinearGroup (Fin 4) K

/-- The determinant twist as an actual map of invertible matrices. -/
def twistGL (X : GL4 K) : GL4 K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (twist X.val)
    (det_twist_ne_zero X.val (Matrix.GeneralLinearGroup.det_ne_zero X))

@[simp] theorem coe_twistGL (X : GL4 K) : (twistGL X).val = twist X.val := rfl

/-- Central determinant scaling defines a group homomorphism on `GL₄`. -/
def twistHom : GL4 K →* GL4 K where
  toFun := twistGL
  map_one' := Units.ext twist_one
  map_mul' X Y := Units.ext (twist_mul X.val Y.val)

theorem twistGL_inverse (X : GL4 K) : twistGL X⁻¹ = (twistGL X)⁻¹ := by
  exact map_inv twistHom X

theorem twistGL_eq_iff (X Y : GL4 K) :
    twistGL X = twistGL Y ↔ ∃ a : rootsOfUnity 3 K, Y.val = (a.val : K) • X.val := by
  rw [Units.ext_iff]
  exact twist_eq_iff_rootsOfUnity X.val Y.val
    (Matrix.GeneralLinearGroup.det_ne_zero X) (Matrix.GeneralLinearGroup.det_ne_zero Y)

theorem twistGL_surjective [IsAlgClosed K] : Function.Surjective (twistGL : GL4 K → GL4 K) := by
  intro Z
  obtain ⟨X, hX, hXZ⟩ := exists_twist_preimage Z.val (Matrix.GeneralLinearGroup.det_ne_zero Z)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hX, ?_⟩
  apply Units.ext
  exact hXZ

/-- The actual central scalar embedding of the field's cube roots of unity. -/
def scalarCubeRoot : rootsOfUnity 3 K →* GL4 K :=
  (Matrix.GeneralLinearGroup.scalar (Fin 4)).comp (rootsOfUnity 3 K).subtype

@[simp] theorem coe_scalarCubeRoot (a : rootsOfUnity 3 K) :
    (scalarCubeRoot a).val = (a.val : K) • (1 : Mat4 K) := by
  change Matrix.scalar (Fin 4) (a.val : K) = _
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/-- The kernel is exactly the actual scalar `μ₃` subgroup. -/
theorem twistHom_kernel :
    (twistHom : GL4 K →* GL4 K).ker = (scalarCubeRoot : rootsOfUnity 3 K →* GL4 K).range := by
  ext X
  change twistGL X = 1 ↔ ∃ a : rootsOfUnity 3 K, scalarCubeRoot a = X
  constructor
  · intro h
    have hm : twist (1 : Mat4 K) = twist X.val := by
      simpa only [twist_one, coe_twistGL, Units.val_one] using congrArg Units.val h.symm
    obtain ⟨a, ha⟩ := (twist_eq_iff_rootsOfUnity (1 : Mat4 K) X.val (by simp)
      (Matrix.GeneralLinearGroup.det_ne_zero X)).mp hm
    exact ⟨a, Units.ext (by rw [coe_scalarCubeRoot]; exact ha.symm)⟩
  · rintro ⟨a, rfl⟩
    apply Units.ext
    rw [coe_twistGL, coe_scalarCubeRoot, twist_smul_cubeRoot _ (by simp) _
      ((mem_rootsOfUnity' 3 a.val).mp a.property), twist_one]
    rfl

theorem twistGL_central_invariant (X : GL4 K) (a : rootsOfUnity 3 K) :
    twistGL (scalarCubeRoot a * X) = twistGL X := by
  change twistHom (scalarCubeRoot a * X) = twistHom X
  rw [map_mul]
  have h : scalarCubeRoot a ∈ (twistHom : GL4 K →* GL4 K).ker := by
    rw [twistHom_kernel]
    exact ⟨a, rfl⟩
  rw [MonoidHom.mem_ker.mp h, one_mul]

/-- The abstract group quotient by this kernel. This is a quotient of groups
of field-valued points, not a coordinate-ring invariant statement. -/
def kernelGroupQuotientEquiv [IsAlgClosed K] :
    GL4 K ⧸ (twistHom : GL4 K →* GL4 K).ker ≃* GL4 K :=
  QuotientGroup.quotientKerEquivOfSurjective twistHom twistGL_surjective

theorem complex_twistGL_surjective : Function.Surjective (twistGL : GL4 ℂ → GL4 ℂ) :=
  twistGL_surjective

end M9.DeterminantTwist

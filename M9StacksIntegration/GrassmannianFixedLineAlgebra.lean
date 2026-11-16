module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-! An actual split quotient of a fourteen-dimensional vector space by
any prescribed nonzero vector, with matrix identities preserved over
arbitrary coefficient rings. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open scoped BigOperators Matrix

universe u v
namespace M9Native.GrassmannianFixedLineAlgebra

variable (K : Type u) [Field K]
abbrev V := Fin 14 → K
abbrev W := Fin 13 → K

def headVector : V K := Fin.cons 1 (fun _ => 0)

theorem headVector_ne_zero : headVector K ≠ 0 := by
  intro h
  have h' := congrFun h 0
  exact one_ne_zero (by simpa only [headVector, Fin.cons_zero, Pi.zero_apply] using h')

/-- A genuine linear automorphism sends the prescribed vector to the first
standard vector. It is extended from the actual one-dimensional spans. -/
theorem exists_normalizer (v : V K) (hv : v ≠ 0) :
    ∃ g : V K ≃ₗ[K] V K, g v = headVector K := by
  let eV := LinearEquiv.toSpanNonzeroSingleton K (V K) v hv
  let eH := LinearEquiv.toSpanNonzeroSingleton K (V K) (headVector K) (headVector_ne_zero K)
  let f := eV.symm ≪≫ₗ eH
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  have h := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  have hv1 : eV.symm ⟨v, Submodule.mem_span_singleton_self v⟩ = 1 :=
    LinearEquiv.coord_self K (V K) v hv
  have hf : (f ⟨v, Submodule.mem_span_singleton_self v⟩ : V K) = headVector K := by
    change (eH (eV.symm ⟨v, Submodule.mem_span_singleton_self v⟩) : V K) = _
    rw [hv1]
    exact congrArg Subtype.val
      (LinearEquiv.toSpanNonzeroSingleton_one K (V K) (headVector K) (headVector_ne_zero K))
  exact h.symm.trans hf

def normalizer (v : V K) (hv : v ≠ 0) : V K ≃ₗ[K] V K :=
  Classical.choose (exists_normalizer K v hv)

theorem normalizer_vector (v : V K) (hv : v ≠ 0) :
    normalizer K v hv v = headVector K :=
  Classical.choose_spec (exists_normalizer K v hv)

def tailMap : V K →ₗ[K] W K where
  toFun := fun x j => x j.succ
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def consZeroMap : W K →ₗ[K] V K where
  toFun := fun (x : W K) => Fin.cons (0 : K) x
  map_add' := by
    intro x y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl
  map_smul' := by
    intro a x
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl

def quotientLinear (v : V K) (hv : v ≠ 0) : V K →ₗ[K] W K :=
  (tailMap K).comp (normalizer K v hv).toLinearMap

def splittingLinear (v : V K) (hv : v ≠ 0) : W K →ₗ[K] V K :=
  (normalizer K v hv).symm.toLinearMap.comp (consZeroMap K)

def coefficientLinear (v : V K) (hv : v ≠ 0) : V K →ₗ[K] K :=
  (LinearMap.proj 0).comp (normalizer K v hv).toLinearMap

theorem quotient_splitting (v : V K) (hv : v ≠ 0) :
    (quotientLinear K v hv).comp (splittingLinear K v hv) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext j
  change normalizer K v hv ((normalizer K v hv).symm (Fin.cons 0 x)) j.succ = x j
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem quotient_vector (v : V K) (hv : v ≠ 0) : quotientLinear K v hv v = 0 := by
  ext j
  change normalizer K v hv v j.succ = 0
  rw [normalizer_vector]
  rfl

theorem coefficient_vector (v : V K) (hv : v ≠ 0) : coefficientLinear K v hv v = 1 := by
  change normalizer K v hv v 0 = 1
  rw [normalizer_vector]
  rfl

/-- The complementary projector is literally a rank-one map with the
prescribed vector, rather than a dimension-only kernel calculation. -/
theorem splitting_quotient_apply (v : V K) (hv : v ≠ 0) (x : V K) :
    splittingLinear K v hv (quotientLinear K v hv x) =
      x - (coefficientLinear K v hv x) • v := by
  apply (normalizer K v hv).injective
  change normalizer K v hv
    ((normalizer K v hv).symm (Fin.cons 0 (fun j => normalizer K v hv x j.succ))) =
      normalizer K v hv (x - (normalizer K v hv x 0) • v)
  rw [LinearEquiv.apply_symm_apply, map_sub, map_smul, normalizer_vector]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [headVector]
  · simp [headVector]

def quotientMatrix (v : V K) (hv : v ≠ 0) : Matrix (Fin 13) (Fin 14) K :=
  LinearMap.toMatrix' (quotientLinear K v hv)

def splittingMatrix (v : V K) (hv : v ≠ 0) : Matrix (Fin 14) (Fin 13) K :=
  LinearMap.toMatrix' (splittingLinear K v hv)

def coefficients (v : V K) (hv : v ≠ 0) : Fin 14 → K :=
  fun j => coefficientLinear K v hv (Pi.single j 1)

theorem quotientMatrix_splittingMatrix (v : V K) (hv : v ≠ 0) :
    quotientMatrix K v hv * splittingMatrix K v hv = 1 := by
  rw [quotientMatrix, splittingMatrix, ← LinearMap.toMatrix'_comp,
    quotient_splitting, LinearMap.toMatrix'_id]

theorem quotientMatrix_vector (v : V K) (hv : v ≠ 0) :
    (quotientMatrix K v hv).mulVec v = 0 := by
  rw [quotientMatrix, LinearMap.toMatrix'_mulVec, quotient_vector]

theorem splittingMatrix_quotientMatrix (v : V K) (hv : v ≠ 0) :
    splittingMatrix K v hv * quotientMatrix K v hv =
      1 - Matrix.of (fun i j => v i * coefficients K v hv j) := by
  rw [quotientMatrix, splittingMatrix, ← LinearMap.toMatrix'_comp]
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearMap.comp_apply, splitting_quotient_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.one_apply, Matrix.of_apply, coefficients, Pi.single_apply]
  simp only [mul_comm]

/-- Every coefficient ring retains the actual rectangular splitting. -/
theorem mapped_quotient_splitting {R : Type v} [CommRing R] (κ : K →+* R)
    (v : V K) (hv : v ≠ 0) :
    (quotientMatrix K v hv).map κ * (splittingMatrix K v hv).map κ = 1 := by
  rw [← Matrix.map_mul, quotientMatrix_splittingMatrix]
  exact Matrix.map_one κ (map_zero κ) (map_one κ)

/-- The discarded projector remains the prescribed scalar-extended line
on every ring, including rings with nilpotents. -/
theorem mapped_splitting_quotient {R : Type v} [CommRing R] (κ : K →+* R)
    (v : V K) (hv : v ≠ 0) :
    (splittingMatrix K v hv).map κ * (quotientMatrix K v hv).map κ =
      1 - Matrix.of (fun i j => κ (v i) * κ (coefficients K v hv j)) := by
  rw [← Matrix.map_mul, splittingMatrix_quotientMatrix]
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, map_sub,
    map_mul]
  split_ifs <;> simp

theorem mapped_quotient_vector {R : Type v} [CommRing R] (κ : K →+* R)
    (v : V K) (hv : v ≠ 0) :
    ((quotientMatrix K v hv).map κ).mulVec (fun i => κ (v i)) = 0 := by
  have h := congrArg (fun x : W K => fun i => κ (x i)) (quotientMatrix_vector K v hv)
  funext i
  have hi := congrFun h i
  change (∑ j : Fin 14, κ (quotientMatrix K v hv i j) * κ (v j)) = 0
  simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] using hi

end M9Native.GrassmannianFixedLineAlgebra

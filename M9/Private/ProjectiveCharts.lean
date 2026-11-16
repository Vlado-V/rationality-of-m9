/-
Ported from the OAI projective-chart constructions in math-main.
The source project is released under the Apache 2.0 license.
The selected OAI files contain no separate per-file copyright headers.
Exact source paths, SHA256 values, and selected bodies are recorded in
`audits/projective-function-field/provenance.json`.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000



/-! # Projective Space -/

namespace M9.ProjectiveGeometry.ProjectiveSpace

noncomputable section

/-!
# Standard complex projective space

The scheme is literally the projective spectrum of the polynomial ring with
its standard grading. Its structure map uses the proved identification of the
degree-zero ring with the complex numbers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The base scheme for complex algebraic geometry. -/
abbrev complexBase : Scheme := Spec (.of ℂ)

/-- The standard homogeneous coordinate ring in `n + 1` variables. -/
abbrev homogeneousCoordinateRing (n : ℕ) := MvPolynomial (Fin (n + 1)) ℂ

/-- The usual grading by total degree. -/
abbrev projectiveGrading (n : ℕ) : ℕ → Submodule ℂ (homogeneousCoordinateRing n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ

instance projectiveGradedAlgebra (n : ℕ) : GradedAlgebra (projectiveGrading n) :=
  MvPolynomial.gradedAlgebra

/-- Complex projective `n`-space as the genuine scheme `Proj ℂ[X₀,...,Xₙ]`. -/
abbrev projectiveSpace (n : ℕ) : Scheme := AlgebraicGeometry.Proj (projectiveGrading n)

/-- The degree-zero ring of the homogeneous coordinate ring consists exactly
of the constant complex polynomials. -/
def degreeZeroConstants (n : ℕ) : ℂ ≃+* projectiveGrading n 0 where
  toFun z := ⟨MvPolynomial.C z, MvPolynomial.isHomogeneous_C (Fin (n + 1)) z⟩
  invFun p := p.val.coeff 0
  left_inv z := MvPolynomial.coeff_zero_C z
  right_inv p := by
    apply Subtype.ext
    have hp : MvPolynomial.IsHomogeneous p.val 0 := p.property
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hp)).symm
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul MvPolynomial.C z w
  map_add' z w := by
    apply Subtype.ext
    exact map_add MvPolynomial.C z w

@[simp]
theorem degreeZeroConstants_coe (n : ℕ) (z : ℂ) :
    (degreeZeroConstants n z : homogeneousCoordinateRing n) = MvPolynomial.C z := rfl

@[simp]
theorem degreeZeroConstants_symm_apply (n : ℕ) (p : projectiveGrading n 0) :
    (degreeZeroConstants n).symm p = p.val.coeff 0 := rfl

/-- The standard structure morphism `ℙⁿ_ℂ → Spec ℂ`. -/
def projectiveSpaceToBase (n : ℕ) : projectiveSpace n ⟶ complexBase :=
  Proj.toSpecZero (projectiveGrading n) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants n).toRingHom)

/-- On every standard homogeneous chart, the structure morphism is induced
by constants followed by the canonical map to the degree-zero localization. -/
theorem projectiveSpaceToBase_chart (n : ℕ) (m : ℕ)
    (f : homogeneousCoordinateRing n) (hf : f ∈ projectiveGrading n m) (hm : 0 < m) :
    Proj.awayι (projectiveGrading n) f hf hm ≫ projectiveSpaceToBase n =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading n) (Submonoid.powers f)).comp
          (degreeZeroConstants n).toRingHom)) := by
  rw [projectiveSpaceToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end

end M9.ProjectiveGeometry.ProjectiveSpace

namespace M9.ProjectiveGeometry.Dehomogenization

noncomputable section
open MvPolynomial

variable {ι R K : Type*}

/-- Insert a coordinate equal to one into an affine coordinate vector. -/
noncomputable def insertOne [One R] (i : ι) (x : {j : ι // j ≠ i} → R) : ι → R := by
  classical
  exact fun j => if h : j = i then 1 else x ⟨j, h⟩

@[simp]
theorem insertOne_self [One R] (i : ι) (x : {j : ι // j ≠ i} → R) :
    insertOne i x i = 1 := by
  classical
  simp [insertOne]

@[simp]
theorem insertOne_of_ne [One R] (i j : ι) (x : {j : ι // j ≠ i} → R) (hj : j ≠ i) :
    insertOne i x j = x ⟨j, hj⟩ := by
  classical
  simp [insertOne, hj]

/-- Polynomial substitution defining the affine equation on the `i`-th patch. -/
noncomputable def dehomogenize [CommSemiring R] (i : ι) :
    MvPolynomial ι R →+* MvPolynomial {j : ι // j ≠ i} R :=
  eval₂Hom C (insertOne i X)

@[simp]
theorem dehomogenize_C [CommSemiring R] (i : ι) (r : R) :
    dehomogenize i (C r) = C r := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_self [CommSemiring R] (i : ι) :
    dehomogenize (R := R) i (X i) = 1 := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_of_ne [CommSemiring R] (i j : ι) (hj : j ≠ i) :
    dehomogenize (R := R) i (X j) = X ⟨j, hj⟩ := by
  simp [dehomogenize, hj]

/-- Evaluation commutes with the concrete dehomogenizing substitution. -/
theorem eval_dehomogenize [CommSemiring R] (i : ι) (f : MvPolynomial ι R)
    (x : {j : ι // j ≠ i} → R) :
    eval x (dehomogenize i f) = eval (insertOne i x) f := by
  classical
  change eval x (eval₂ C (insertOne i X) f) = _
  rw [← eval_assoc]
  apply congrArg (fun v : ι → R => eval v f)
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.comp_apply, hj]

end
end M9.ProjectiveGeometry.Dehomogenization

namespace M9.ProjectiveGeometry.HomogeneousEvalMap

open scoped BigOperators

section
variable {K σ : Type*}

/-- Evaluating a homogeneous polynomial on a scaled coordinate vector multiplies
its value by the corresponding power of the scalar. -/
theorem eval_smul_of_isHomogeneous [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : K) (v : σ → K) :
    MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hf (MvPolynomial.mem_support_iff.mp hm)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_apply, hm']
  ac_rfl

end

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S]

/-- Homogeneous evaluation scales by the degree even after mapping the
coefficients into a different commutative semiring. -/
theorem eval₂_smul_of_isHomogeneous {f : MvPolynomial ι R} {d : ℕ}
    (hf : f.IsHomogeneous d) (φ : R →+* S) (c : S) (v : ι → S) :
    MvPolynomial.eval₂ φ (c • v) f = c ^ d * MvPolynomial.eval₂ φ v f := by
  simpa only [MvPolynomial.eval_map] using
    eval_smul_of_isHomogeneous (hf.map φ) c v

/-- The target-ring formulation with coordinate multiplication written
explicitly instead of function-space scalar multiplication. -/
theorem eval₂_mul_of_isHomogeneous {f : MvPolynomial ι R} {d : ℕ}
    (hf : f.IsHomogeneous d) (φ : R →+* S) (c : S) (v : ι → S) :
    MvPolynomial.eval₂ φ (fun i => c * v i) f =
      c ^ d * MvPolynomial.eval₂ φ v f :=
  eval₂_smul_of_isHomogeneous hf φ c v

end M9.ProjectiveGeometry.HomogeneousEvalMap


/-! # Projective Chart To Polynomial -/

namespace M9.ProjectiveGeometry.ProjectiveChartToPolynomial

noncomputable section

/-!
# The actual standard Proj chart maps to its polynomial coordinate ring

This uses the homogeneous localization that occurs in mathlib's affine chart
isomorphism for `Proj`, rather than a separate model of projective points.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open M9.ProjectiveGeometry.Dehomogenization

/-- The homogeneous localization defining the standard `i`-th Proj chart. -/
abbrev projectiveChartRing (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)

/-- The affine polynomial coordinate ring, omitting the `i`-th variable. -/
abbrev projectiveChartPolynomial (n : ℕ) (i : Fin (n + 1)) :=
  MvPolynomial {j : Fin (n + 1) // j ≠ i} ℂ

theorem projectiveVariable_homogeneous (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ ProjectiveSpace.projectiveGrading n 1 :=
  MvPolynomial.isHomogeneous_X ℂ i

/-- Constant coefficients in the actual homogeneous chart ring. -/
def projectiveChartConstants (n : ℕ) (i : Fin (n + 1)) :
    ℂ →+* projectiveChartRing n i :=
  (HomogeneousLocalization.fromZeroRingHom (ProjectiveSpace.projectiveGrading n)
    (Submonoid.powers (MvPolynomial.X i))).comp (ProjectiveSpace.degreeZeroConstants n).toRingHom

/-- Setting `Xᵢ = 1` extends to the ordinary localization at `Xᵢ`. -/
def projectiveChartLocalizationToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) →+*
      projectiveChartPolynomial n i :=
  Localization.awayLift (Dehomogenization.dehomogenize i) (MvPolynomial.X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

/-- Dehomogenization restricted to the actual degree-zero localization. -/
def projectiveChartToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartRing n i →+* projectiveChartPolynomial n i :=
  (projectiveChartLocalizationToPolynomial n i).comp
    (algebraMap (projectiveChartRing n i)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)))

/-- A homogeneous fraction `f / Xᵢ^k` maps exactly to `f(Xᵢ:= 1)`. -/
@[simp]
theorem projectiveChartToPolynomial_mk (n : ℕ) (i : Fin (n + 1))
    (k : ℕ) (f : ProjectiveSpace.homogeneousCoordinateRing n)
    (hf : f ∈ ProjectiveSpace.projectiveGrading n (k • (1 : ℕ))) :
    projectiveChartToPolynomial n i
      (HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
        (projectiveVariable_homogeneous n i) k f hf) = Dehomogenization.dehomogenize i f := by
  change Localization.awayLift (Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk f ⟨MvPolynomial.X i ^ k, k, rfl⟩) = _
  simpa using Localization.awayLift_mk (Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) f 1 (by simp) k

/-- Dehomogenization preserves the coefficient homomorphism to the chart. -/
@[simp]
theorem projectiveChartToPolynomial_constants (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    projectiveChartToPolynomial n i (projectiveChartConstants n i c) =
      MvPolynomial.C c := by
  change Localization.awayLift (Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk (MvPolynomial.C c) ⟨1, Submonoid.one_mem _⟩) = _
  simpa using Localization.awayLift_mk (Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) (MvPolynomial.C c) 1 (by simp) 0

end

end M9.ProjectiveGeometry.ProjectiveChartToPolynomial


/-! # Polynomial To Projective Chart -/

namespace M9.ProjectiveGeometry.PolynomialToProjectiveChart

noncomputable section

/-!
# Polynomial coordinates are the actual homogeneous localization chart

Variables map to the degree-zero homogeneous fractions `X_j / X_i`. The inverse
identities use homogeneous polynomial evaluation in the ordinary localization,
so this comparison identifies actual rings used by the scheme `Proj`.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open M9.ProjectiveGeometry.Dehomogenization

/-- A degree-zero coordinate fraction in the actual standard Proj chart. -/
def projectiveChartRatio (n : ℕ) (i j : Fin (n + 1)) : ProjectiveChartToPolynomial.projectiveChartRing n i :=
  HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
    (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) 1 (MvPolynomial.X j)
    (by simpa using ProjectiveChartToPolynomial.projectiveVariable_homogeneous n j)

@[simp]
theorem projectiveChartToPolynomial_ratio (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    ProjectiveChartToPolynomial.projectiveChartToPolynomial n i (projectiveChartRatio n i j.val) = X j := by
  simp [projectiveChartRatio, j.property]

/-- Map an affine polynomial into the homogeneous chart by coordinate ratios. -/
def polynomialToProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveChartToPolynomial.projectiveChartPolynomial n i →+* ProjectiveChartToPolynomial.projectiveChartRing n i :=
  MvPolynomial.eval₂Hom (ProjectiveChartToPolynomial.projectiveChartConstants n i)
    (fun j => projectiveChartRatio n i j.val)

@[simp]
theorem polynomialToProjectiveChart_C (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    polynomialToProjectiveChart n i (C c) = ProjectiveChartToPolynomial.projectiveChartConstants n i c := by
  simp [polynomialToProjectiveChart]

@[simp]
theorem polynomialToProjectiveChart_X (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    polynomialToProjectiveChart n i (X j) = projectiveChartRatio n i j.val := by
  simp [polynomialToProjectiveChart]

/-- Substitution back to affine polynomials is a left inverse. -/
theorem projectiveChartToPolynomial_comp (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i).comp (polynomialToProjectiveChart n i) =
      RingHom.id (ProjectiveChartToPolynomial.projectiveChartPolynomial n i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- The constants in the homogeneous chart have their expected value in the
ordinary localization. -/
@[simp]
theorem projectiveChartConstants_val (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    (ProjectiveChartToPolynomial.projectiveChartConstants n i c).val =
      algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (C c) := by
  change Localization.mk (C c) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- Coordinate fractions have their expected value in the ordinary localization. -/
theorem projectiveChartRatio_val (n : ℕ) (i j : Fin (n + 1)) :
    (projectiveChartRatio n i j).val =
      algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (X j) *
      IsLocalization.Away.invSelf (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) := by
  simp only [projectiveChartRatio, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  rfl

/-- General homogeneous chart fractions have the expected inverse-power denominator. -/
theorem projectiveChartFraction_val (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (hf : f ∈ ProjectiveSpace.projectiveGrading n (k • (1 : ℕ))) :
    (HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
      (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) k f hf).val =
      IsLocalization.Away.invSelf (S := Localization.Away
        (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))
        (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) ^ k *
      algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) f := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
  congr 1
  simpa only [one_pow, SubmonoidClass.mk_pow, IsLocalization.Away.invSelf] using
    (IsLocalization.mk'_pow
      (S := Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))
      (1 : ProjectiveSpace.homogeneousCoordinateRing n)
      (⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ :
        Submonoid.powers (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) k)

/-- Substitution by ratios in the ordinary localization is normalization of
all homogeneous variables by the same inverse of `X_i`. -/
theorem projectiveChart_normalization_map (n : ℕ) (i : Fin (n + 1)) :
    ((algebraMap (ProjectiveChartToPolynomial.projectiveChartRing n i)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp
      (polynomialToProjectiveChart n i)).comp (Dehomogenization.dehomogenize i) =
    MvPolynomial.eval₂Hom
      ((algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp C)
      (fun j => IsLocalization.Away.invSelf
        (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) *
        algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
          (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [RingHom.comp_apply, Dehomogenization.dehomogenize_X_self, map_one, eval₂Hom_X']
      rw [mul_comm, IsLocalization.Away.mul_invSelf]
    · simp [hj, projectiveChartRatio_val, mul_comm]

/-- Evaluation of all original variables through their localization images
is the localization homomorphism itself. -/
theorem projectiveChart_unnormalized_map (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.eval₂Hom
      ((algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp C)
      (fun j => algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (X j)) =
    algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- Every homogeneous chart fraction is the polynomial in coordinate ratios
obtained by dehomogenizing its numerator. -/
theorem polynomialToProjectiveChart_dehomogenize (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (hf : f ∈ ProjectiveSpace.projectiveGrading n (k • (1 : ℕ))) :
    polynomialToProjectiveChart n i (Dehomogenization.dehomogenize i f) =
      HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) k f hf := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  change (((algebraMap (ProjectiveChartToPolynomial.projectiveChartRing n i)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp
      (polynomialToProjectiveChart n i)).comp (Dehomogenization.dehomogenize i)) f = _
  rw [projectiveChart_normalization_map, projectiveChartFraction_val]
  have hhom : f.IsHomogeneous k := by simpa using hf
  rw [MvPolynomial.coe_eval₂Hom, HomogeneousEvalMap.eval₂_mul_of_isHomogeneous hhom]
  congr 1
  exact RingHom.congr_fun (projectiveChart_unnormalized_map n i) f

/-- Dehomogenization is also a right inverse on every actual chart fraction. -/
theorem polynomialToProjectiveChart_comp (n : ℕ) (i : Fin (n + 1)) :
    (polynomialToProjectiveChart n i).comp (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i) =
      RingHom.id (ProjectiveChartToPolynomial.projectiveChartRing n i) := by
  apply RingHom.ext
  intro x
  obtain ⟨k, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (ProjectiveSpace.projectiveGrading n) (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) x
  simpa only [RingHom.comp_apply, RingHom.id_apply, ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk] using
    polynomialToProjectiveChart_dehomogenize n i k f hf

/-- The standard scheme chart ring is canonically the polynomial ring in all
homogeneous coordinate ratios except the normalized coordinate. -/
def projectiveChartRingEquiv (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveChartToPolynomial.projectiveChartRing n i ≃+* ProjectiveChartToPolynomial.projectiveChartPolynomial n i where
  toFun := ProjectiveChartToPolynomial.projectiveChartToPolynomial n i
  invFun := polynomialToProjectiveChart n i
  left_inv x := RingHom.congr_fun (polynomialToProjectiveChart_comp n i) x
  right_inv x := RingHom.congr_fun (projectiveChartToPolynomial_comp n i) x
  map_add' := map_add (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)
  map_mul' := map_mul (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)

@[simp]
theorem projectiveChartRingEquiv_apply (n : ℕ) (i : Fin (n + 1))
    (x : ProjectiveChartToPolynomial.projectiveChartRing n i) :
    projectiveChartRingEquiv n i x = ProjectiveChartToPolynomial.projectiveChartToPolynomial n i x := rfl

@[simp]
theorem projectiveChartRingEquiv_symm_apply (n : ℕ) (i : Fin (n + 1))
    (p : ProjectiveChartToPolynomial.projectiveChartPolynomial n i) :
    (projectiveChartRingEquiv n i).symm p = polynomialToProjectiveChart n i p := rfl

end

end M9.ProjectiveGeometry.PolynomialToProjectiveChart


/-! # Projective Coordinate Cover -/

namespace M9.ProjectiveGeometry.ProjectiveCoordinateCover

noncomputable section

/-!
# The finite coordinate affine cover of the actual projective scheme

The variables generate the irrelevant ideal of the standard polynomial grading.
Consequently the usual coordinate basic opens cover `Proj ℂ[X₀,...,Xₙ]`.
This file concerns the genuine scheme, not its as-yet separately constructed
ordinary complex topology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Every positive-degree homogeneous polynomial lies in the ideal of variables. -/
theorem positive_homogeneous_mem_coordinateIdeal (n d : ℕ) (hd : 0 < d)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (hf : f ∈ ProjectiveSpace.projectiveGrading n d) :
    f ∈ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → ProjectiveSpace.homogeneousCoordinateRing n)) := by
  have hpow : f ∈ MvPolynomial.idealOfVars (Fin (n + 1)) ℂ ^ 1 := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have hdeg : m.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hf (MvPolynomial.mem_support_iff.mp hm)
    simpa only [hdeg] using (Nat.succ_le_iff.mpr hd)
  simpa only [pow_one] using hpow

/-- The irrelevant ideal in the standard polynomial grading is generated by the variables. -/
theorem projective_irrelevant_eq_coordinateIdeal (n : ℕ) :
    (HomogeneousIdeal.irrelevant (ProjectiveSpace.projectiveGrading n)).toIdeal =
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → ProjectiveSpace.homogeneousCoordinateRing n)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le (ProjectiveSpace.projectiveGrading n)).mpr
    intro d hd f hf
    exact positive_homogeneous_mem_coordinateIdeal n d hd f hf
  · rw [Ideal.span_le]
    rintro f ⟨i, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem (ProjectiveSpace.projectiveGrading n) (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X ℂ i)

/-- The usual coordinate open `Xᵢ ≠ 0` inside the genuine projective scheme. -/
abbrev projectiveCoordinateOpen (n : ℕ) (i : Fin (n + 1)) : (ProjectiveSpace.projectiveSpace n).Opens :=
  Proj.basicOpen (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)

@[simp]
theorem mem_projectiveCoordinateOpen (n : ℕ) (i : Fin (n + 1)) (x : ProjectiveSpace.projectiveSpace n) :
    x ∈ projectiveCoordinateOpen n i ↔ MvPolynomial.X i ∉ x.asHomogeneousIdeal :=
  Proj.mem_basicOpen (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) x

/-- Coordinate opens cover the projective scheme. -/
theorem iSup_projectiveCoordinateOpen (n : ℕ) :
    (⨆ i, projectiveCoordinateOpen n i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact (projective_irrelevant_eq_coordinateIdeal n).le

/-- In particular, every scheme point belongs to at least one coordinate chart. -/
theorem exists_mem_projectiveCoordinateOpen (n : ℕ) (x : ProjectiveSpace.projectiveSpace n) :
    ∃ i, x ∈ projectiveCoordinateOpen n i := by
  apply TopologicalSpace.Opens.mem_iSup.mp
  rw [iSup_projectiveCoordinateOpen]
  trivial

/-- The finite standard affine open cover, with chart rings the actual degree-zero localizations. -/
def projectiveCoordinateAffineCover (n : ℕ) : (ProjectiveSpace.projectiveSpace n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (ProjectiveSpace.projectiveGrading n)
    (fun (i : Fin (n + 1)) => MvPolynomial.X i)
    (m := fun _ => 1)
    (fun i => MvPolynomial.isHomogeneous_X ℂ i)
    (fun _ => by decide)
    (projective_irrelevant_eq_coordinateIdeal n).le

/-- Its indexing type has precisely the `n + 1` standard coordinates. -/
@[simp]
theorem projectiveCoordinateAffineCover_index (n : ℕ) :
    (projectiveCoordinateAffineCover n).I₀ = Fin (n + 1) := rfl

/-- Each coordinate basic open is affine. -/
theorem projectiveCoordinateOpen_isAffine (n : ℕ) (i : Fin (n + 1)) :
    IsAffineOpen (projectiveCoordinateOpen n i) :=
  Proj.isAffineOpen_basicOpen (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i) (by decide : 0 < 1)

end

end M9.ProjectiveGeometry.ProjectiveCoordinateCover


/-! # Projective Chart -/

namespace M9.ProjectiveGeometry.ProjectiveChart

noncomputable section

/-!
# Standard coordinate charts of the actual projective scheme

The coordinate basic open of `Proj ℂ[X₀,...,Xₙ]` is identified with the spectrum
of the polynomial ring in the remaining `n` coordinates, and hence with
mathlib's actual affine-space scheme. The isomorphisms commute with the given
morphisms to `Spec ℂ`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The coefficient-field structure map on the polynomial affine chart. -/
abbrev projectiveChartPolynomialToBase (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) ⟶ ProjectiveSpace.complexBase :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* ProjectiveChartToPolynomial.projectiveChartPolynomial n i))

@[simp]
theorem projectiveChartRingEquiv_coe (n : ℕ) (i : Fin (n + 1)) :
    (PolynomialToProjectiveChart.projectiveChartRingEquiv n i : ProjectiveChartToPolynomial.projectiveChartRing n i →+* ProjectiveChartToPolynomial.projectiveChartPolynomial n i) =
      ProjectiveChartToPolynomial.projectiveChartToPolynomial n i := by
  ext x
  rfl

/-- The genuine coordinate basic open is the affine spectrum of its polynomial
coordinate ring, by the proved homogeneous-localization ring equivalence. -/
def projectiveCoordinateIsoSpec (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toScheme ≅ Spec (.of (ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) :=
  Proj.basicOpenIsoSpec (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso (PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm.toCommRingCatIso.op

/-- On the inverse chart map, the scheme morphism is induced by the explicit
ring homomorphism sending homogeneous fractions to dehomogenized polynomials. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_ι (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec n i).inv ≫ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι =
      Spec.map (CommRingCat.ofHom (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)) ≫
        Proj.awayι (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
          (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1) := by
  simp [projectiveCoordinateIsoSpec, Proj.awayι, Category.assoc]

/-- The inverse chart identification is a morphism over the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec n i).inv ≫ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫
      ProjectiveSpace.projectiveSpaceToBase n = projectiveChartPolynomialToBase n i := by
  rw [projectiveCoordinateIsoSpec_inv_ι_assoc, ProjectiveSpace.projectiveSpaceToBase_chart]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact ProjectiveChartToPolynomial.projectiveChartToPolynomial_constants n i c

/-- The chart isomorphism respects the actual structure morphisms to `Spec ℂ`. -/
@[reassoc]
theorem projectiveCoordinateIsoSpec_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec n i).hom ≫ projectiveChartPolynomialToBase n i =
      (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫ ProjectiveSpace.projectiveSpaceToBase n := by
  apply (cancel_epi (projectiveCoordinateIsoSpec n i).inv).mp
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
    (projectiveCoordinateIsoSpec_inv_over n i).symm

/-- The same chart comparison as an isomorphism in the category over `Spec ℂ`. -/
def projectiveCoordinateOverIso (n : ℕ) (i : Fin (n + 1)) :
    Over.mk ((ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫ ProjectiveSpace.projectiveSpaceToBase n) ≅
      Over.mk (projectiveChartPolynomialToBase n i) :=
  Over.isoMk (projectiveCoordinateIsoSpec n i) (projectiveCoordinateIsoSpec_over n i)

/-- The standard polynomial affine chart map into projective space. -/
def projectiveAffineChartMap (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) ⟶ ProjectiveSpace.projectiveSpace n :=
  (projectiveCoordinateIsoSpec n i).inv ≫ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι

instance (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (projectiveAffineChartMap n i) := by
  dsimp [projectiveAffineChartMap]
  infer_instance

@[reassoc]
theorem projectiveAffineChartMap_over (n : ℕ) (i : Fin (n + 1)) :
    projectiveAffineChartMap n i ≫ ProjectiveSpace.projectiveSpaceToBase n =
      projectiveChartPolynomialToBase n i := by
  exact projectiveCoordinateIsoSpec_inv_over n i

/-- The omitted-coordinate index has exactly `n` elements. -/
theorem projectiveChartCoordinate_card (n : ℕ) (i : Fin (n + 1)) :
    Fintype.card {j : Fin (n + 1) // j ≠ i} = n := by
  rw [Fintype.card_subtype_compl (fun j : Fin (n + 1) => j = i)]
  simp

/-- Each actual projective coordinate open is mathlib's affine `n`-space,
indexed by the `n` homogeneous coordinates other than the normalized one. -/
def projectiveCoordinateIsoAffineSpace (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toScheme ≅
      AffineSpace {j : Fin (n + 1) // j ≠ i} ProjectiveSpace.complexBase :=
  projectiveCoordinateIsoSpec n i ≪≫
    (AffineSpace.SpecIso {j : Fin (n + 1) // j ≠ i} (.of ℂ)).symm

/-- The identification with native affine space also respects the complex base. -/
@[reassoc]
theorem projectiveCoordinateIsoAffineSpace_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoAffineSpace n i).hom ≫
      (AffineSpace {j : Fin (n + 1) // j ≠ i} ProjectiveSpace.complexBase ↘ ProjectiveSpace.complexBase) =
      (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫ ProjectiveSpace.projectiveSpaceToBase n := by
  change ((projectiveCoordinateIsoSpec n i).hom ≫
      (AffineSpace.SpecIso {j : Fin (n + 1) // j ≠ i} (.of ℂ)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over]
  exact projectiveCoordinateIsoSpec_over n i

end

end M9.ProjectiveGeometry.ProjectiveChart

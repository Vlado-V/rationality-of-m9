module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-!
# The actual determinant-one signed permutation group in dimension three

The four projective diagonals of Section 4.1 are used to construct a concrete
matrix for every permutation. Rational calculations are checked by the kernel;
the resulting matrices are then transported to the complex special orthogonal
group. Their image is proved to consist of exactly the determinant-one signed
permutation matrices.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace M9.TetrahedralGroup

open scoped BigOperators

abbrev S4 := Equiv.Perm (Fin 4)
abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

/-- The four actual diagonal vectors, with the order used in the paper. -/
def diagonalQ : Fin 4 → Fin 3 → ℚ :=
  ![![1,1,1], ![1,-1,-1], ![-1,1,-1], ![-1,-1,1]]

/-- The ordinary tetrahedral representation in the diagonal coordinates. -/
def frameMatrixQ (π : S4) : Mat3 ℚ :=
  fun i j => (∑ a : Fin 4, diagonalQ (π a) i * diagonalQ a j) / 4

/-- The determinant twist makes every tetrahedral symmetry a rotation. -/
def determinant3 (M : Mat3 ℚ) : ℚ :=
  M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 -
    M 0 2 * M 1 1 * M 2 0 - M 0 1 * M 1 0 * M 2 2 - M 0 0 * M 1 2 * M 2 1

theorem determinant3_eq_det (M : Mat3 ℚ) : determinant3 M = M.det := by
  rw [Matrix.det_fin_three]
  unfold determinant3
  ring

def orientationQ (π : S4) : ℚ := determinant3 (frameMatrixQ π)

def rotationQ (π : S4) : Mat3 ℚ := orientationQ π • frameMatrixQ π

theorem rotationQ_one : rotationQ 1 = 1 := by decide +kernel

theorem rotationQ_mul : ∀ π τ : S4, rotationQ (π*τ) = rotationQ π * rotationQ τ := by decide +kernel

theorem rotationQ_det : ∀ π : S4, (rotationQ π).det = 1 := by
  simp_rw [← determinant3_eq_det]
  decide +kernel

theorem rotationQ_orthogonal : ∀ π : S4, rotationQ π * (rotationQ π).transpose = 1 := by decide +kernel

theorem rotationQ_action : ∀ (π : S4) (a : Fin 4),
    (rotationQ π).mulVec (diagonalQ a) = orientationQ π • diagonalQ (π a) := by decide +kernel

theorem orientationQ_sign : ∀ π : S4, orientationQ π = 1 ∨ orientationQ π = -1 := by decide +kernel

theorem rotationQ_injective : Function.Injective rotationQ := by decide +kernel

/-- A signed permutation matrix, using a row permutation and one sign per row. -/
def signedMatrix (K : Type*) [CommRing K] (σ : Equiv.Perm (Fin 3))
    (ε : Fin 3 → Bool) : Mat3 K :=
  fun i j => if j = σ i then if ε i then -1 else 1 else 0

theorem rotationQ_signed : ∀ π : S4, ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
    rotationQ π = signedMatrix ℚ σ ε := by decide +kernel

theorem signedQ_det_one_range : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
    determinant3 (signedMatrix ℚ σ ε) = 1 → ∃ π : S4, rotationQ π = signedMatrix ℚ σ ε := by
  decide +kernel

theorem signedQ_orthogonal : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
    signedMatrix ℚ σ ε * (signedMatrix ℚ σ ε).transpose = 1 := by decide +kernel

theorem diagonalQ_cross_witness : ∀ a b : Fin 4, a ≠ b →
    ∃ i j : Fin 3, diagonalQ a i * diagonalQ b j ≠ diagonalQ b i * diagonalQ a j := by decide +kernel

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℂ

/-- The actual complex matrices obtained by coefficient inclusion. -/
def complexMatrix (π : S4) : Mat3 ℂ := (rotationQ π).map (algebraMap ℚ ℂ)

theorem complexMatrix_one : complexMatrix 1 = 1 := by
  simp [complexMatrix, rotationQ_one]

theorem complexMatrix_mul (π τ : S4) :
    complexMatrix (π*τ) = complexMatrix π * complexMatrix τ := by
  exact (congrArg ((algebraMap ℚ ℂ).mapMatrix) (rotationQ_mul π τ)).trans
    ((algebraMap ℚ ℂ).mapMatrix.map_mul _ _)

theorem complexMatrix_det (π : S4) : (complexMatrix π).det = 1 := by
  calc
    _ = algebraMap ℚ ℂ (rotationQ π).det := ((algebraMap ℚ ℂ).map_det _).symm
    _ = 1 := by rw [rotationQ_det, map_one]

theorem complexMatrix_orthogonal (π : S4) :
    complexMatrix π * (complexMatrix π).transpose = 1 := by
  change (rotationQ π).map (algebraMap ℚ ℂ) *
    ((rotationQ π).map (algebraMap ℚ ℂ)).transpose = 1
  have h := congrArg ((algebraMap ℚ ℂ).mapMatrix) (rotationQ_orthogonal π)
  rw [← Matrix.transpose_map]
  exact ((algebraMap ℚ ℂ).mapMatrix.map_mul _ _).symm.trans (h.trans (map_one _))

/-- An actual representation in the complex special orthogonal group. -/
def rho : S4 →* SO3 where
  toFun π := ⟨complexMatrix π, Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℂ).mpr (complexMatrix_orthogonal π), complexMatrix_det π⟩⟩
  map_one' := Subtype.ext complexMatrix_one
  map_mul' π τ := Subtype.ext (complexMatrix_mul π τ)

@[simp] theorem rho_val (π : S4) : (rho π).val = complexMatrix π := rfl

theorem complexMatrix_injective : Function.Injective complexMatrix := by
  intro π τ h
  apply rotationQ_injective
  funext i j
  apply (algebraMap ℚ ℂ).injective
  exact congrArg (fun M => M i j) h

theorem rho_injective : Function.Injective rho := by
  intro π τ h
  exact complexMatrix_injective (congrArg Subtype.val h)

theorem signedMatrix_map (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    (signedMatrix ℚ σ ε).map (algebraMap ℚ ℂ) = signedMatrix ℂ σ ε := by
  funext i j
  by_cases h : j = σ i <;> cases hb : ε i <;> simp [signedMatrix, h, hb]

def IsSignedPermutation (M : Mat3 ℂ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool), M = signedMatrix ℂ σ ε

theorem rho_isSignedPermutation (π : S4) : IsSignedPermutation (rho π).val := by
  obtain ⟨σ,ε,h⟩ := rotationQ_signed π
  exact ⟨σ,ε,(congrArg ((algebraMap ℚ ℂ).mapMatrix) h).trans (signedMatrix_map σ ε)⟩

/-- Every determinant-one signed permutation is one of the actual matrices
above; this is a classification theorem, not a cardinality premise. -/
theorem exists_rho_of_signed (g : SO3) (hg : IsSignedPermutation g.val) :
    ∃ π : S4, rho π = g := by
  obtain ⟨σ,ε,hg⟩ := hg
  have hdet : (signedMatrix ℚ σ ε).det = 1 := by
    apply (algebraMap ℚ ℂ).injective
    calc
      _ = ((signedMatrix ℚ σ ε).map (algebraMap ℚ ℂ)).det := (algebraMap ℚ ℂ).map_det _
      _ = (signedMatrix ℂ σ ε).det := congrArg Matrix.det (signedMatrix_map σ ε)
      _ = 1 := hg ▸ g.property.2
      _ = _ := (map_one _).symm
  obtain ⟨π,hπ⟩ := signedQ_det_one_range σ ε ((determinant3_eq_det _).trans hdet)
  refine ⟨π, Subtype.ext ?_⟩
  exact ((congrArg ((algebraMap ℚ ℂ).mapMatrix) hπ).trans (signedMatrix_map σ ε)).trans hg.symm

/-- The concrete group: those actual special orthogonal matrices which are
signed permutation matrices. -/
def gammaSubgroup : Subgroup SO3 where
  carrier := fun g => IsSignedPermutation g.val
  one_mem' := by
    change IsSignedPermutation (1 : SO3).val
    rw [← map_one rho]
    exact rho_isSignedPermutation 1
  mul_mem' := by
    intro g h hg hh
    obtain ⟨π,rfl⟩ := exists_rho_of_signed g hg
    obtain ⟨τ,rfl⟩ := exists_rho_of_signed h hh
    change IsSignedPermutation (rho π * rho τ).val
    rw [← map_mul]
    exact rho_isSignedPermutation (π*τ)
  inv_mem' := by
    intro g hg
    obtain ⟨π,rfl⟩ := exists_rho_of_signed g hg
    change IsSignedPermutation ((rho π)⁻¹).val
    rw [← map_inv]
    exact rho_isSignedPermutation π⁻¹

abbrev Gamma := gammaSubgroup

/-- The actual inclusion as complex matrices. -/
def matrix (g : Gamma) : Mat3 ℂ := g.val.val

theorem matrix_isSignedPermutation (g : Gamma) : IsSignedPermutation (matrix g) := g.property

theorem matrix_det (g : Gamma) : (matrix g).det = 1 := g.val.property.2

theorem matrix_orthogonal (g : Gamma) : matrix g * (matrix g).transpose = 1 :=
  (Matrix.mem_orthogonalGroup_iff (Fin 3) ℂ).mp g.val.property.1

theorem signed_orthogonal (M : Mat3 ℂ) (hM : IsSignedPermutation M) :
    M * M.transpose = 1 := by
  obtain ⟨σ,ε,rfl⟩ := hM
  have h := congrArg ((algebraMap ℚ ℂ).mapMatrix) (signedQ_orthogonal σ ε)
  rw [← signedMatrix_map σ ε, ← Matrix.transpose_map]
  exact ((algebraMap ℚ ℂ).mapMatrix.map_mul _ _).symm.trans (h.trans (map_one _))

/-- Membership as actual complex matrices is precisely the determinant-one
signed permutation condition in the manuscript. -/
theorem exists_gamma_iff (M : Mat3 ℂ) :
    (∃ g : Gamma, matrix g = M) ↔ IsSignedPermutation M ∧ M.det = 1 := by
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨matrix_isSignedPermutation g, matrix_det g⟩
  · rintro ⟨hs,hd⟩
    let g : SO3 := ⟨M, Matrix.mem_specialOrthogonalGroup_iff.mpr
      ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℂ).mpr (signed_orthogonal M hs), hd⟩⟩
    exact ⟨⟨g,hs⟩,rfl⟩

def gammaOfPermutation : S4 →* Gamma := rho.codRestrict gammaSubgroup rho_isSignedPermutation

theorem gammaOfPermutation_bijective : Function.Bijective gammaOfPermutation := by
  constructor
  · intro π τ h
    exact rho_injective (congrArg Subtype.val h)
  · intro g
    obtain ⟨π,hπ⟩ := exists_rho_of_signed g.val g.property
    exact ⟨π,Subtype.ext hπ⟩

/-- The permutation of the four actual projective diagonals. -/
def framePermutation : Gamma ≃* S4 :=
  (MulEquiv.ofBijective gammaOfPermutation gammaOfPermutation_bijective).symm

instance : Fintype Gamma := Fintype.ofEquiv S4 framePermutation.symm.toEquiv

theorem card_gamma : Fintype.card Gamma = 24 := by
  rw [Fintype.card_congr framePermutation.toEquiv, Fintype.card_perm, Fintype.card_fin]
  decide

theorem gammaOfPermutation_framePermutation (g : Gamma) :
    gammaOfPermutation (framePermutation g) = g := framePermutation.symm_apply_apply g

/-- The diagonal vectors in the original complex coordinate space. -/
def diagonal (a : Fin 4) : Fin 3 → ℂ := fun i => algebraMap ℚ ℂ (diagonalQ a i)

def orientation (π : S4) : ℂ := algebraMap ℚ ℂ (orientationQ π)

theorem orientation_ne_zero (π : S4) : orientation π ≠ 0 := by
  rcases orientationQ_sign π with h | h <;> simp [orientation,h]

theorem rho_diagonal (π : S4) (a : Fin 4) :
    (rho π).val.mulVec (diagonal a) = orientation π • diagonal (π a) := by
  funext i
  have h := congrArg (fun v => algebraMap ℚ ℂ (v i)) (rotationQ_action π a)
  change ((rotationQ π).map (algebraMap ℚ ℂ)).mulVec
    (fun j => algebraMap ℚ ℂ (diagonalQ a j)) i =
      algebraMap ℚ ℂ (orientationQ π) * algebraMap ℚ ℂ (diagonalQ (π a) i)
  simp only [RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul] at h
  exact h

/-- The displayed group isomorphism is realized by its literal action on
the four lines, with a nonzero common projective multiplier. -/
theorem matrix_diagonal (g : Gamma) (a : Fin 4) :
    (matrix g).mulVec (diagonal a) =
      orientation (framePermutation g) • diagonal (framePermutation g a) := by
  have h := rho_diagonal (framePermutation g) a
  have hg := congrArg (fun x : Gamma => x.val.val) (gammaOfPermutation_framePermutation g)
  change complexMatrix (framePermutation g) = matrix g at hg
  change (complexMatrix (framePermutation g)).mulVec (diagonal a) = _ at h
  rw [hg] at h
  exact h

/-- The four actual projective points, represented as one-dimensional spans. -/
def frameLine (a : Fin 4) : Submodule ℂ (Fin 3 → ℂ) := ℂ ∙ diagonal a

theorem diagonal_ne_zero (a : Fin 4) : diagonal a ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have ha : diagonalQ a 0 ≠ 0 := by
    have hall : ∀ b : Fin 4, diagonalQ b 0 ≠ 0 := by decide +kernel
    exact hall a
  apply ha
  apply (algebraMap ℚ ℂ).injective
  exact h0.trans (map_zero _).symm

theorem frameLine_injective : Function.Injective frameLine := by
  intro a b hab
  by_contra hne
  obtain ⟨i,j,hij⟩ := diagonalQ_cross_witness a b hne
  have hmem : diagonal a ∈ frameLine a := Submodule.mem_span_singleton_self (diagonal a)
  rw [hab] at hmem
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  have heq : diagonal a i * diagonal b j = diagonal b i * diagonal a j := by
    rw [← hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  apply hij
  apply (algebraMap ℚ ℂ).injective
  rw [map_mul, map_mul]
  exact heq

theorem map_frameLine (g : Gamma) (a : Fin 4) :
    (frameLine a).map (matrix g).mulVecLin = frameLine (framePermutation g a) := by
  rw [frameLine, Submodule.map_span, Set.image_singleton]
  change (ℂ ∙ (matrix g).mulVec (diagonal a)) = _
  rw [matrix_diagonal]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
    (orientation_ne_zero (framePermutation g))) _

/-- The permutation action on the four projective points is faithful. -/
theorem eq_one_of_fixes_frame (g : Gamma)
    (hg : ∀ a, (frameLine a).map (matrix g).mulVecLin = frameLine a) : g = 1 := by
  apply framePermutation.injective
  rw [map_one]
  apply Equiv.ext
  intro a
  apply frameLine_injective
  exact (map_frameLine g a).symm.trans (hg a)

/-- In odd dimension three, a scalar special orthogonal matrix is the identity. -/
theorem SO3_scalar_eq_one (g : SO3) (c : ℂ) (hg : g.val = c • (1 : Mat3 ℂ)) : g = 1 := by
  have ho : g.val * g.val.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℂ).mp g.property.1
  rw [hg, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul] at ho
  have hc2 : c*c = 1 := by simpa using congrArg (fun M => M 0 0) ho
  have hc3 : c^3 = 1 := by simpa [hg] using g.property.2
  have hc : c = 1 := by
    calc
      c = (c*c)*c := by rw [hc2, one_mul]
      _ = c^3 := by ring
      _ = 1 := hc3
  apply Subtype.ext
  simpa [hc] using hg

theorem scalar_eq_one (g : Gamma) (c : ℂ) (hg : matrix g = c • (1 : Mat3 ℂ)) : g = 1 :=
  Subtype.ext (SO3_scalar_eq_one g.val c hg)

theorem rho_scalar_eq_one (π : S4) (c : ℂ) (hπ : (rho π).val = c • (1 : Mat3 ℂ)) : π = 1 := by
  apply rho_injective
  exact (SO3_scalar_eq_one (rho π) c hπ).trans (map_one rho).symm

end M9.TetrahedralGroup

module

public import M9.FrameAction
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# The standard pencil of conics and its projective frame

This leaf treats the literal pencil from Section 4.1, using actual symmetric
matrices and projective points.  The classification results below concern
projective frames; generic-pencil diagonalization is a separate obligation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.ConicPencilFrames

open scoped BigOperators

abbrev Vec3 := Fin 3 → ℂ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev Conic := M9.Symmetric3 ℂ
abbrev GL3 := FrameAction.GL3 ℂ

/-- Actual homogeneous quadratic evaluation associated with a symmetric matrix. -/
def quadraticValue (Q : Conic) (v : Vec3) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, v i * Q.val i j * v j

theorem quadraticValue_coordinates (Q : Conic) (v : Vec3) :
    quadraticValue Q v = Q.val 0 0 * v 0 ^ 2 + Q.val 1 1 * v 1 ^ 2 +
      Q.val 2 2 * v 2 ^ 2 + 2 * Q.val 0 1 * v 0 * v 1 +
      2 * Q.val 0 2 * v 0 * v 2 + 2 * Q.val 1 2 * v 1 * v 2 := by
  have h10 : Q.val 1 0 = Q.val 0 1 := congrFun (congrFun Q.property 0) 1
  have h20 : Q.val 2 0 = Q.val 0 2 := congrFun (congrFun Q.property 0) 2
  have h21 : Q.val 2 1 = Q.val 1 2 := congrFun (congrFun Q.property 1) 2
  simp only [quadraticValue, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.isValue, Fin.succ_zero_eq_one, Fin.reduceSucc, add_zero, h10, h20, h21]
  ring

theorem quadraticValue_smul (Q : Conic) (c : ℂ) (v : Vec3) :
    quadraticValue Q (c • v) = c ^ 2 * quadraticValue Q v := by
  simp only [quadraticValue_coordinates, Pi.smul_apply, smul_eq_mul]
  ring

theorem quadraticValue_add (Q R : Conic) (v : Vec3) :
    quadraticValue (Q + R) v = quadraticValue Q v + quadraticValue R v := by
  simp only [quadraticValue, Submodule.coe_add, Matrix.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib]

theorem quadraticValue_smul_conic (c : ℂ) (Q : Conic) (v : Vec3) :
    quadraticValue (c • Q) v = c * quadraticValue Q v := by
  simp only [quadraticValue, Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul]
  simp [mul_left_comm, mul_assoc, Finset.mul_sum]

def diagonalConic (a b c : ℂ) : Conic :=
  ⟨Matrix.diagonal ![a,b,c], by
    change (Matrix.diagonal ![a,b,c]).transpose = Matrix.diagonal ![a,b,c]
    exact Matrix.diagonal_transpose _⟩

/-- The two conics `x²-y²` and `y²-z²`. -/
def standardFirst : Conic := diagonalConic 1 (-1) 0
def standardSecond : Conic := diagonalConic 0 1 (-1)

def standardPencil : Submodule ℂ Conic :=
  Submodule.span ℂ {standardFirst, standardSecond}

@[simp] theorem quadraticValue_first (v : Vec3) :
    quadraticValue standardFirst v = v 0 ^ 2 - v 1 ^ 2 := by
  simp [quadraticValue_coordinates, standardFirst, diagonalConic, sub_eq_add_neg]

@[simp] theorem quadraticValue_second (v : Vec3) :
    quadraticValue standardSecond v = v 1 ^ 2 - v 2 ^ 2 := by
  simp [quadraticValue_coordinates, standardSecond, diagonalConic, sub_eq_add_neg]

/-- The literal common-zero condition for every conic in a pencil. -/
def BaseVector (P : Submodule ℂ Conic) (v : Vec3) : Prop :=
  ∀ Q ∈ P, quadraticValue Q v = 0

theorem baseVector_standard_iff (v : Vec3) :
    BaseVector standardPencil v ↔ v 0 ^ 2 = v 1 ^ 2 ∧ v 1 ^ 2 = v 2 ^ 2 := by
  constructor
  · intro h
    constructor
    · have hh := h standardFirst (Submodule.subset_span (by simp))
      simpa only [quadraticValue_first, sub_eq_zero] using hh
    · have hh := h standardSecond (Submodule.subset_span (by simp))
      simpa only [quadraticValue_second, sub_eq_zero] using hh
  · rintro ⟨h01,h12⟩ Q hQ
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hQ
    simp [quadraticValue_add, quadraticValue_smul_conic, h01, h12]

theorem diagonal_is_baseVector (i : Fin 4) :
    BaseVector standardPencil (TetrahedralGroup.diagonal i) := by
  apply (baseVector_standard_iff _).mpr
  fin_cases i <;> norm_num [TetrahedralGroup.diagonal, TetrahedralGroup.diagonalQ]

/-- The standard pencil has exactly four nonzero common-zero directions. -/
theorem standard_baseVector_classification (v : Vec3) (hv : v ≠ 0) :
    BaseVector standardPencil v ↔
      ∃ i : Fin 4, ∃ c : ℂ, c ≠ 0 ∧ v = c • TetrahedralGroup.diagonal i := by
  constructor
  · intro h
    obtain ⟨h01,h12⟩ := (baseVector_standard_iff v).mp h
    have hx : v 0 ≠ 0 := by
      intro hz
      have hy : v 1 = 0 := by simpa [hz] using h01.symm
      have hzz : v 2 = 0 := by simpa [hy] using h12.symm
      apply hv
      funext i
      fin_cases i <;> simp [hz,hy,hzz]
    have hy : v 1 = v 0 ∨ v 1 = -v 0 :=
      sq_eq_sq_iff_eq_or_eq_neg.mp h01.symm
    have hz : v 2 = v 0 ∨ v 2 = -v 0 :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (h01.trans h12).symm
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · refine ⟨0,v 0,hx,?_⟩
      funext i
      fin_cases i <;> simp [TetrahedralGroup.diagonal,TetrahedralGroup.diagonalQ,hy,hz]
    · refine ⟨3,-v 0,neg_ne_zero.mpr hx,?_⟩
      funext i
      fin_cases i <;> simp [TetrahedralGroup.diagonal,TetrahedralGroup.diagonalQ,hy,hz]
    · refine ⟨2,-v 0,neg_ne_zero.mpr hx,?_⟩
      funext i
      fin_cases i <;> simp [TetrahedralGroup.diagonal,TetrahedralGroup.diagonalQ,hy,hz]
    · refine ⟨1,v 0,hx,?_⟩
      funext i
      fin_cases i <;> simp [TetrahedralGroup.diagonal,TetrahedralGroup.diagonalQ,hy,hz]
  · rintro ⟨i,c,_,rfl⟩ Q hQ
    rw [quadraticValue_smul, diagonal_is_baseVector i Q hQ, mul_zero]

/-- The four actual projective basepoints. -/
def standardPoint (i : Fin 4) : Projectivization ℂ Vec3 :=
  Projectivization.mk ℂ (TetrahedralGroup.diagonal i) (TetrahedralGroup.diagonal_ne_zero i)

theorem standardPoint_injective : Function.Injective standardPoint := by
  intro i j h
  apply TetrahedralGroup.frameLine_injective
  exact congrArg Projectivization.submodule h

theorem standard_projective_base_locus (v : Vec3) (hv : v ≠ 0) :
    BaseVector standardPencil v ↔
      Projectivization.mk ℂ v hv ∈ Set.range standardPoint := by
  rw [standard_baseVector_classification v hv]
  constructor
  · rintro ⟨i,c,hc,rfl⟩
    refine ⟨i,?_⟩
    apply ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,rfl⟩).symm
  · rintro ⟨i,hi⟩
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hi.symm
    refine ⟨i,c,?_,hc.symm⟩
    intro hc0
    apply hv
    simpa [hc0] using hc.symm

/-- Four general-position basepoints recover the literal standard pencil:
every quadratic form vanishing at these four points lies in their pencil. -/
theorem conic_in_standardPencil_iff (Q : Conic) :
    Q ∈ standardPencil ↔ ∀ i : Fin 4, quadraticValue Q (TetrahedralGroup.diagonal i) = 0 := by
  constructor
  · intro hQ i
    exact diagonal_is_baseVector i Q hQ
  · intro hQ
    have h0 := hQ 0
    have h1 := hQ 1
    have h2 := hQ 2
    have h3 := hQ 3
    norm_num [quadraticValue_coordinates, TetrahedralGroup.diagonal,
      TetrahedralGroup.diagonalQ] at h0 h1 h2 h3
    have h01 : Q.val 0 1 = 0 := by linear_combination (h0-h1-h2+h3)/8
    have h02 : Q.val 0 2 = 0 := by linear_combination (h0-h1+h2-h3)/8
    have h12 : Q.val 1 2 = 0 := by linear_combination (h0+h1-h2-h3)/8
    have htr : Q.val 0 0 + Q.val 1 1 + Q.val 2 2 = 0 := by
      linear_combination (h0+h1+h2+h3)/4
    have h10 : Q.val 1 0 = 0 := (congrFun (congrFun Q.property 0) 1).trans h01
    have h20 : Q.val 2 0 = 0 := (congrFun (congrFun Q.property 0) 2).trans h02
    have h21 : Q.val 2 1 = 0 := (congrFun (congrFun Q.property 1) 2).trans h12
    apply Submodule.mem_span_pair.mpr
    refine ⟨Q.val 0 0,-Q.val 2 2,?_⟩
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardFirst,standardSecond,diagonalConic,h01,h02,h12,h10,h20,h21]
    linear_combination -htr

/-- The first three diagonal vectors, viewed as the columns of a matrix. -/
def standardFrameMatrix : Mat3 :=
  fun i j => TetrahedralGroup.diagonal j.castSucc i

theorem det_standardFrameMatrix : standardFrameMatrix.det = 4 := by
  norm_num [standardFrameMatrix,TetrahedralGroup.diagonal,TetrahedralGroup.diagonalQ,
    Matrix.det_fin_three]

def standardFrameGL : GL3 := Matrix.GeneralLinearGroup.mkOfDetNeZero
  standardFrameMatrix (by rw [det_standardFrameMatrix]; norm_num)

/-- The fourth vector is minus the sum of the first three, with all coefficients nonzero. -/
theorem diagonal_sum : (∑ i : Fin 3, TetrahedralGroup.diagonal i.castSucc) =
    -TetrahedralGroup.diagonal 3 := by
  funext j
  fin_cases j <;>
    norm_num [TetrahedralGroup.diagonal,TetrahedralGroup.diagonalQ,Fin.sum_univ_succ]

/-- Every choice of three of the four points is linearly independent. -/
theorem diagonal_triple_independent (f : Fin 3 → Fin 4) (hf : Function.Injective f) :
    LinearIndependent ℂ (fun i => TetrahedralGroup.diagonal (f i)) := by
  apply Matrix.linearIndependent_cols_of_det_ne_zero
    (A := fun i j => TetrahedralGroup.diagonal (f j) i)
  have hdet : ∀ (a b c : Fin 4), a ≠ b → a ≠ c → b ≠ c →
      Matrix.det (fun i j : Fin 3 => TetrahedralGroup.diagonal (![a,b,c] j) i) ≠ 0 := by
    intro a b c hab hac hbc
    rw [Matrix.det_fin_three]
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp_all [TetrahedralGroup.diagonal,TetrahedralGroup.diagonalQ] <;>
      norm_num
  have hfun : f = ![f 0,f 1,f 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun]
  apply hdet
  · exact hf.ne (by decide)
  · exact hf.ne (by decide)
  · exact hf.ne (by decide)

/-- The first three frame vectors form a genuine vector-space basis. -/
def standardBasis : Module.Basis (Fin 3) ℂ Vec3 :=
  basisOfLinearIndependentOfCardEqFinrank
    (diagonal_triple_independent Fin.castSucc (by
      intro i j hij
      exact Fin.castSucc_inj.mp hij)) (by simp)

@[simp] theorem standardBasis_apply (i : Fin 3) :
    standardBasis i = TetrahedralGroup.diagonal i.castSucc := by simp [standardBasis]

/-- A linear map preserving each of the four standard directions is scalar.
The statement does not assume the map is invertible. -/
theorem scalar_of_fixes_standard_directions (f : Vec3 →ₗ[ℂ] Vec3)
    (h : ∀ i : Fin 4, ∃ c : ℂ, f (TetrahedralGroup.diagonal i) = c • TetrahedralGroup.diagonal i) :
    ∃ c : ℂ, f = c • LinearMap.id := by
  choose c hc using h
  have hsum : (∑ i : Fin 3, (c i.castSucc - c 3) • TetrahedralGroup.diagonal i.castSucc) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← map_sum, ← Finset.smul_sum, ← hc]
    rw [diagonal_sum, map_neg, hc, smul_neg, sub_self]
  have heq : ∀ i : Fin 3, c i.castSucc = c 3 := by
    have hh := (Fintype.linearIndependent_iff.mp standardBasis.linearIndependent)
      (fun i => c i.castSucc - c 3) (by simpa only [standardBasis_apply] using hsum)
    intro i
    exact sub_eq_zero.mp (hh i)
  refine ⟨c 3,standardBasis.ext fun i => ?_⟩
  simpa only [standardBasis_apply, LinearMap.smul_apply, LinearMap.id_apply, heq] using hc i.castSucc

theorem matrix_scalar_of_fixes_standard_directions (M : Mat3)
    (h : ∀ i : Fin 4, ∃ c : ℂ,
      M.mulVec (TetrahedralGroup.diagonal i) = c • TetrahedralGroup.diagonal i) :
    ∃ c : ℂ, M = c • 1 := by
  obtain ⟨c,hc⟩ := scalar_of_fixes_standard_directions M.mulVecLin h
  refine ⟨c,?_⟩
  apply Matrix.toLin'.injective
  simpa [Matrix.toLin'_apply'] using hc

/-- A genuine ordered projective frame: every three representatives are independent. -/
def IsProjectiveFrame (v : Fin 4 → Vec3) : Prop :=
  ∀ f : Fin 3 → Fin 4, Function.Injective f → LinearIndependent ℂ (fun i => v (f i))

theorem standard_isProjectiveFrame : IsProjectiveFrame TetrahedralGroup.diagonal :=
  diagonal_triple_independent

def frameBasis (v : Fin 4 → Vec3) (hv : IsProjectiveFrame v) : Module.Basis (Fin 3) ℂ Vec3 :=
  basisOfLinearIndependentOfCardEqFinrank (hv Fin.castSucc (by
    intro i j hij
    exact Fin.castSucc_inj.mp hij)) (by simp)

@[simp] theorem frameBasis_apply (v : Fin 4 → Vec3) (hv : IsProjectiveFrame v) (i : Fin 3) :
    frameBasis v hv i = v i.castSucc := by simp [frameBasis]

/-- No coordinate of the fourth point in the basis of the first three can vanish. -/
theorem frameBasis_last_coord_ne_zero (v : Fin 4 → Vec3) (hv : IsProjectiveFrame v)
    (i : Fin 3) : (frameBasis v hv).repr (v 3) i ≠ 0 := by
  intro hz
  let b := frameBasis v hv
  let w : Fin 3 → Vec3 := fun j => v (i.castSucc.succAbove j)
  have hli : LinearIndependent ℂ w := hv _ Fin.succAbove_right_injective
  let b' : Module.Basis (Fin 3) ℂ Vec3 :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hzero : b.coord i = 0 := by
    apply b'.ext
    intro j
    change b.repr (b' j) i = 0
    have hb' : b' j = w j := by simp [b']
    rw [hb']
    rcases Fin.eq_castSucc_or_eq_last (i.castSucc.succAbove j) with ⟨k,hk⟩ | hk
    · have hki : k ≠ i := by
        intro hki
        subst k
        exact Fin.succAbove_ne i.castSucc j hk
      change b.repr (v (i.castSucc.succAbove j)) i = 0
      rw [hk]
      have hbk : v k.castSucc = b k := (frameBasis_apply v hv k).symm
      rw [hbk]
      simp [hki]
    · change b.repr (v (i.castSucc.succAbove j)) i = 0
      simpa only [b,hk,show Fin.last 3 = (3 : Fin 4) from rfl] using hz
  have hh := LinearMap.congr_fun hzero (b i)
  simp at hh

/-- A concrete change of coordinates sending the standard frame to any ordered frame. -/
theorem exists_linearEquiv_of_projectiveFrame (v : Fin 4 → Vec3) (hv : IsProjectiveFrame v) :
    ∃ e : Vec3 ≃ₗ[ℂ] Vec3, ∃ c : Fin 4 → ℂ,
      (∀ i, c i ≠ 0) ∧ ∀ i, e (TetrahedralGroup.diagonal i) = c i • v i := by
  let b := frameBasis v hv
  let w : Fin 3 → ℂ := fun i => -b.repr (v 3) i
  have hw (i : Fin 3) : IsUnit (w i) :=
    isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (frameBasis_last_coord_ne_zero v hv i))
  let b' := b.isUnitSMul hw
  let e : Vec3 ≃ₗ[ℂ] Vec3 := standardBasis.equiv b' (Equiv.refl (Fin 3))
  have he (i : Fin 3) : e (TetrahedralGroup.diagonal i.castSucc) = w i • v i.castSucc := by
    rw [← standardBasis_apply i]
    rw [Module.Basis.equiv_apply]
    simp [b',Module.Basis.isUnitSMul_apply,b]
  have he3 : e (TetrahedralGroup.diagonal 3) = v 3 := by
    have hh := congrArg e diagonal_sum
    simp only [map_sum, map_neg, he] at hh
    have hs : (∑ i : Fin 3, w i • v i.castSucc) = -v 3 := by
      simp only [w, ← frameBasis_apply v hv, neg_smul, Finset.sum_neg_distrib]
      exact congrArg Neg.neg (b.sum_repr (v 3))
    rw [hs] at hh
    exact neg_injective hh.symm
  refine ⟨e,Fin.snoc w 1,?_,?_⟩
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩ | rfl
    · simpa using (hw j).ne_zero
    · change Fin.snoc (α := fun _ : Fin 4 => ℂ) w 1 (Fin.last 3) ≠ 0
      rw [Fin.snoc_last]
      exact one_ne_zero
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩ | rfl
    · simpa using he j
    · simpa only [show (3 : Fin 4) = Fin.last 3 from rfl,Fin.snoc_last,one_smul] using he3

/-- Vector action of an actual invertible matrix. -/
def vectorEquiv (M : GL3) : Vec3 ≃ₗ[ℂ] Vec3 where
  toFun := (M : Mat3).mulVec
  invFun := (↑M⁻¹ : Mat3).mulVec
  left_inv v := by simp [Matrix.mulVec_mulVec]
  right_inv v := by simp [Matrix.mulVec_mulVec]
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _

@[simp] theorem vectorEquiv_apply (M : GL3) (v : Vec3) :
    vectorEquiv M v = (M : Mat3).mulVec v := rfl

def pointImage (M : GL3) (L : Projectivization ℂ Vec3) : Projectivization ℂ Vec3 :=
  vectorEquiv M • L

/-- A matrix inducing a specified permutation of the standard points is the
corresponding tetrahedral rotation multiplied by a scalar. -/
theorem scalar_rotation_of_permutation (M : GL3) (π : TetrahedralGroup.S4)
    (h : ∀ i : Fin 4, ∃ c : ℂ,
      (M : Mat3).mulVec (TetrahedralGroup.diagonal i) = c • TetrahedralGroup.diagonal (π i)) :
    ∃ c : ℂ, c ≠ 0 ∧ (M : Mat3) = c • (TetrahedralGroup.rho π).val := by
  let R : Mat3 := (TetrahedralGroup.rho π).val
  let S : Mat3 := (TetrahedralGroup.rho π⁻¹).val
  have hRS : R * S = 1 := by
    change ((TetrahedralGroup.rho π) * (TetrahedralGroup.rho π⁻¹)).val = 1
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hN : ∀ i : Fin 4, ∃ c : ℂ,
      (S * (M : Mat3)).mulVec (TetrahedralGroup.diagonal i) = c • TetrahedralGroup.diagonal i := by
    intro i
    obtain ⟨c,hc⟩ := h i
    refine ⟨c * TetrahedralGroup.orientation π⁻¹,?_⟩
    rw [← Matrix.mulVec_mulVec,hc,Matrix.mulVec_smul]
    have hs : S.mulVec (TetrahedralGroup.diagonal (π i)) =
        TetrahedralGroup.orientation π⁻¹ • TetrahedralGroup.diagonal i := by
      have hpi : π⁻¹ (π i) = i := π.symm_apply_apply i
      simpa only [hpi] using TetrahedralGroup.rho_diagonal π⁻¹ (π i)
    rw [hs,smul_smul]
  obtain ⟨c,hc⟩ := matrix_scalar_of_fixes_standard_directions (S * (M : Mat3)) hN
  have hm : (M : Mat3) = c • R := by
    have hh := congrArg (fun A : Mat3 => R * A) hc
    simpa [← Matrix.mul_assoc,hRS,Matrix.mul_smul] using hh
  refine ⟨c,?_,hm⟩
  intro hc0
  have hm0 : (M : Mat3) = 0 := by simpa only [hc0,zero_smul] using hm
  have h10 : (1 : Mat3) = 0 := by simpa [hm0] using (Units.inv_mul M).symm
  exact one_ne_zero h10

/-- The literal projective stabilizer of the four standard points is exactly
the constructed tetrahedral group, modulo scalar matrices. -/
theorem standard_stabilizer_iff (M : GL3) :
    (∀ i : Fin 4, pointImage M (standardPoint i) ∈ Set.range standardPoint) ↔
      ∃ g : TetrahedralGroup.Gamma, ∃ c : ℂ,
        c ≠ 0 ∧ (M : Mat3) = c • TetrahedralGroup.matrix g := by
  constructor
  · intro h
    choose p hp using h
    have hinj : Function.Injective p := by
      intro i j hij
      apply standardPoint_injective
      apply (MulAction.toPerm (vectorEquiv M)).injective
      exact (hp i).symm.trans ((congrArg standardPoint hij).trans (hp j))
    let π : TetrahedralGroup.S4 := Equiv.ofBijective p
      ⟨hinj,Finite.surjective_of_injective hinj⟩
    have hvec (i : Fin 4) : ∃ c : ℂ,
        (M : Mat3).mulVec (TetrahedralGroup.diagonal i) = c • TetrahedralGroup.diagonal (π i) := by
      have hh := (hp i).symm
      change vectorEquiv M • standardPoint i = standardPoint (π i) at hh
      simp only [standardPoint, Projectivization.smul_mk] at hh
      obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hh
      exact ⟨c,hc.symm⟩
    obtain ⟨c,hc,hm⟩ := scalar_rotation_of_permutation M π hvec
    exact ⟨TetrahedralGroup.gammaOfPermutation π,c,hc,hm⟩
  · rintro ⟨g,c,hc,hm⟩ i
    refine ⟨TetrahedralGroup.framePermutation g i,?_⟩
    change standardPoint _ = vectorEquiv M • standardPoint i
    simp only [standardPoint,Projectivization.smul_mk]
    apply ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ?_).symm
    refine ⟨c * TetrahedralGroup.orientation (TetrahedralGroup.framePermutation g),?_⟩
    change _ = (M : Mat3).mulVec (TetrahedralGroup.diagonal i)
    rw [hm,Matrix.smul_mulVec,TetrahedralGroup.matrix_diagonal,smul_smul]

/-- Converting the frame coordinate change to an actual invertible matrix. -/
def matrixOfEquiv (e : Vec3 ≃ₗ[ℂ] Vec3) : GL3 :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)

@[simp] theorem vectorEquiv_matrixOfEquiv (e : Vec3 ≃ₗ[ℂ] Vec3) :
    vectorEquiv (matrixOfEquiv e) = e := by
  apply LinearEquiv.ext
  intro v
  have h := congrArg (fun A : LinearMap.GeneralLinearGroup ℂ Vec3 => A.toLinearEquiv v)
    (Matrix.GeneralLinearGroup.toLin.apply_symm_apply (LinearMap.GeneralLinearGroup.ofLinearEquiv e))
  exact h

/-- Transitivity on actual ordered projective frames, with all projective scalars explicit. -/
theorem exists_matrix_of_projectiveFrame (v : Fin 4 → Vec3) (hv : IsProjectiveFrame v) :
    ∃ M : GL3, ∃ c : Fin 4 → ℂ,
      (∀ i, c i ≠ 0) ∧ ∀ i,
        (M : Mat3).mulVec (TetrahedralGroup.diagonal i) = c i • v i := by
  obtain ⟨e,c,hc,he⟩ := exists_linearEquiv_of_projectiveFrame v hv
  refine ⟨matrixOfEquiv e,c,hc,fun i => ?_⟩
  simpa only [← vectorEquiv_apply,vectorEquiv_matrixOfEquiv] using he i

/-- The product of all four triple determinants in universal point coordinates. -/
def frameDiscriminant : MvPolynomial (Fin 4 × Fin 3) ℂ :=
  ∏ i : Fin 4, Matrix.det (fun r c : Fin 3 =>
    MvPolynomial.X (i.succAbove c,r))

theorem eval_frameDiscriminant (v : Fin 4 → Vec3) :
    MvPolynomial.eval (fun ij : Fin 4 × Fin 3 => v ij.1 ij.2) frameDiscriminant =
      ∏ i : Fin 4, Matrix.det (fun r c : Fin 3 => v (i.succAbove c) r) := by
  simp only [frameDiscriminant,map_prod,RingHom.map_det]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  funext r c
  change MvPolynomial.eval _ (MvPolynomial.X _) = _
  simp

/-- A nonzero value of this explicit discriminant is exactly projective general position. -/
theorem frameDiscriminant_ne_zero_iff (v : Fin 4 → Vec3) :
    MvPolynomial.eval (fun ij : Fin 4 × Fin 3 => v ij.1 ij.2) frameDiscriminant ≠ 0 ↔
      IsProjectiveFrame v := by
  rw [eval_frameDiscriminant]
  constructor
  · intro h f hf
    have hdet (i : Fin 4) :
        Matrix.det (fun r c : Fin 3 => v (i.succAbove c) r) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
    have hex : ∃ i : Fin 4, ∀ j : Fin 3, f j ≠ i := by
      by_contra! hh
      have hc := Fintype.card_le_of_surjective f hh
      norm_num at hc
    obtain ⟨i,hi⟩ := hex
    choose g hg using fun j => Fin.exists_succAbove_eq (hi j)
    have hgi : Function.Injective g := by
      intro a b hab
      apply hf
      rw [← hg a, ← hg b, hab]
    have hli := Matrix.linearIndependent_cols_of_det_ne_zero (hdet i)
    have hh := hli.comp g hgi
    convert hh using 1
    funext j r
    change v (f j) r = v (i.succAbove (g j)) r
    rw [hg]
  · intro h
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Matrix.nonsingular_iff_det_ne_zero.mp
      (Matrix.Nonsingular.of_linearIndependent_col (h _ Fin.succAbove_right_injective))

theorem frameDiscriminant_nonzero : frameDiscriminant ≠ 0 := by
  intro hz
  have hh := (frameDiscriminant_ne_zero_iff TetrahedralGroup.diagonal).mpr
    standard_isProjectiveFrame
  exact hh (by rw [hz,map_zero])

/-- The displayed nonempty discriminant open consists of genuine ordered frames. -/
theorem frame_discriminant_open_nonempty :
    IsOpen {a : Fin 4 × Fin 3 → ℂ | MvPolynomial.eval a frameDiscriminant ≠ 0} ∧
      Set.Nonempty {a : Fin 4 × Fin 3 → ℂ | MvPolynomial.eval a frameDiscriminant ≠ 0} := by
  constructor
  · exact isOpen_ne.preimage (MvPolynomial.continuous_eval frameDiscriminant)
  · exact ⟨fun ij => TetrahedralGroup.diagonal ij.1 ij.2,
      (frameDiscriminant_ne_zero_iff TetrahedralGroup.diagonal).mpr standard_isProjectiveFrame⟩

/-- Pullback of quadratic forms by an actual invertible coordinate change. -/
def conicPullback (M : GL3) : Conic ≃ₗ[ℂ] Conic where
  toFun Q :=
    ⟨(M : Mat3).transpose * Q.val * (M : Mat3), by
      have hQ : Q.val.transpose = Q.val := Q.property
      change ((M : Mat3).transpose * Q.val * (M : Mat3)).transpose = _
      simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hQ]
      simp only [Matrix.mul_assoc]⟩
  invFun Q :=
    ⟨(↑M⁻¹ : Mat3).transpose * Q.val * (↑M⁻¹ : Mat3), by
      have hQ : Q.val.transpose = Q.val := Q.property
      change ((↑M⁻¹ : Mat3).transpose * Q.val * (↑M⁻¹ : Mat3)).transpose = _
      simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hQ]
      simp only [Matrix.mul_assoc]⟩
  left_inv Q := by
    apply Subtype.ext
    change (↑M⁻¹ : Mat3).transpose * ((M : Mat3).transpose * Q.val * (M : Mat3)) *
      (↑M⁻¹ : Mat3) = Q.val
    have ht : (↑M⁻¹ : Mat3).transpose * (M : Mat3).transpose = 1 := by
      rw [← Matrix.transpose_mul,Units.mul_inv,Matrix.transpose_one]
    calc
      _ = (((↑M⁻¹ : Mat3).transpose * (M : Mat3).transpose) * Q.val) *
        ((M : Mat3) * (↑M⁻¹ : Mat3)) := by simp only [Matrix.mul_assoc]
      _ = Q.val := by rw [ht,Units.mul_inv]; simp
  right_inv Q := by
    apply Subtype.ext
    change (M : Mat3).transpose * ((↑M⁻¹ : Mat3).transpose * Q.val * (↑M⁻¹ : Mat3)) *
      (M : Mat3) = Q.val
    have ht : (M : Mat3).transpose * (↑M⁻¹ : Mat3).transpose = 1 := by
      rw [← Matrix.transpose_mul,Units.inv_mul,Matrix.transpose_one]
    calc
      _ = (((M : Mat3).transpose * (↑M⁻¹ : Mat3).transpose) * Q.val) *
        ((↑M⁻¹ : Mat3) * (M : Mat3)) := by simp only [Matrix.mul_assoc]
      _ = Q.val := by rw [ht,Units.inv_mul]; simp
  map_add' Q R := by apply Subtype.ext; simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' c Q := by apply Subtype.ext; simp

@[simp] theorem conicPullback_val (M : GL3) (Q : Conic) :
    (conicPullback M Q).val = (M : Mat3).transpose * Q.val * (M : Mat3) := rfl

theorem quadraticValue_pullback (M : GL3) (Q : Conic) (v : Vec3) :
    quadraticValue (conicPullback M Q) v = quadraticValue Q ((M : Mat3).mulVec v) := by
  simp only [quadraticValue,conicPullback_val,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.isValue,Fin.succ_zero_eq_one,Fin.reduceSucc,add_zero]
  ring

@[simp] theorem conicPullback_inv_apply (M : GL3) (Q : Conic) :
    conicPullback M⁻¹ (conicPullback M Q) = Q :=
  (conicPullback M).left_inv Q

@[simp] theorem conicPullback_apply_inv (M : GL3) (Q : Conic) :
    conicPullback M (conicPullback M⁻¹ Q) = Q :=
  (conicPullback M).right_inv Q

/-- The conics through a specified ordered quadruple, as an actual submodule. -/
def pencilThrough (v : Fin 4 → Vec3) : Submodule ℂ Conic where
  carrier := {Q | ∀ i, quadraticValue Q (v i) = 0}
  zero_mem' := by intro i; simp [quadraticValue]
  add_mem' := by intro Q R hQ hR i; rw [quadraticValue_add,hQ,hR,add_zero]
  smul_mem' := by intro c Q hQ i; rw [quadraticValue_smul_conic,hQ,mul_zero]

theorem pencilThrough_standard : pencilThrough TetrahedralGroup.diagonal = standardPencil := by
  ext Q
  exact (conic_in_standardPencil_iff Q).symm

theorem mem_pencilThrough_transformed (M : GL3) (Q : Conic) :
    Q ∈ pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i)) ↔
      conicPullback M Q ∈ standardPencil := by
  rw [conic_in_standardPencil_iff]
  exact forall_congr' fun i => by rw [quadraticValue_pullback]

/-- Coordinate pullback identifies every framed pencil with the standard pencil. -/
theorem pencilThrough_transformed_map (M : GL3) :
    (pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i))).map
      (conicPullback M).toLinearMap = standardPencil := by
  ext Q
  constructor
  · rintro ⟨R,hR,rfl⟩
    exact (mem_pencilThrough_transformed M R).mp hR
  · intro hQ
    refine ⟨conicPullback M⁻¹ Q,?_,?_⟩
    · apply (mem_pencilThrough_transformed M _).mpr
      simpa using hQ
    · exact (conicPullback M).right_inv Q

/-- The actual nonzero base vectors of a transformed pencil are exactly the
four transformed standard directions. -/
theorem transformed_baseVector_classification (M : GL3) (v : Vec3) (hv : v ≠ 0) :
    BaseVector (pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i))) v ↔
      ∃ i : Fin 4, ∃ c : ℂ, c ≠ 0 ∧
        v = c • ((M : Mat3).mulVec (TetrahedralGroup.diagonal i)) := by
  let u := (↑M⁻¹ : Mat3).mulVec v
  have hu : u ≠ 0 := by
    intro hz
    have hh := congrArg (vectorEquiv M) hz
    apply hv
    simpa [u,vectorEquiv,Matrix.mulVec_mulVec] using hh
  have hMu : (M : Mat3).mulVec u = v := by simp [u,Matrix.mulVec_mulVec]
  have hbase : BaseVector (pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i))) v ↔
      BaseVector standardPencil u := by
    constructor
    · intro h Q hQ
      have hR : conicPullback M⁻¹ Q ∈ pencilThrough
          (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i)) := by
        apply (mem_pencilThrough_transformed M _).mpr
        simpa using hQ
      simpa only [quadraticValue_pullback] using h _ hR
    · intro h Q hQ
      have hh := h (conicPullback M Q) ((mem_pencilThrough_transformed M Q).mp hQ)
      simpa only [quadraticValue_pullback,hMu] using hh
  rw [hbase,standard_baseVector_classification u hu]
  constructor
  · rintro ⟨i,c,hc,huv⟩
    refine ⟨i,c,hc,?_⟩
    rw [← hMu,huv,Matrix.mulVec_smul]
  · rintro ⟨i,c,hc,hv'⟩
    refine ⟨i,c,hc,?_⟩
    simp [u,hv',Matrix.mulVec_smul,Matrix.mulVec_mulVec]

def standardGenerators : Fin 2 → Conic := ![standardFirst,standardSecond]

theorem standardGenerators_independent : LinearIndependent ℂ standardGenerators := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h0 := congrArg (fun Q : Conic => Q.val 0 0) hc
  have h2 := congrArg (fun Q : Conic => Q.val 2 2) hc
  simp [standardGenerators,Fin.sum_univ_succ,standardFirst,standardSecond,diagonalConic] at h0 h2
  fin_cases i
  · exact h0
  · exact h2

theorem finrank_standardPencil : Module.finrank ℂ standardPencil = 2 := by
  have hs : Set.range standardGenerators = {standardFirst,standardSecond} := by
    ext Q
    simp [standardGenerators,or_comm]
  rw [standardPencil,← hs,finrank_span_eq_card standardGenerators_independent]
  rfl

theorem finrank_pencilThrough_transformed (M : GL3) :
    Module.finrank ℂ (pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i))) = 2 := by
  have hh := (conicPullback M).finrank_map_eq
    (pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i)))
  rw [pencilThrough_transformed_map,finrank_standardPencil] at hh
  exact hh.symm

/-- Four projective-frame points determine a genuine two-dimensional pencil,
and a constructed coordinate change identifies it with the standard pencil. -/
theorem pencilThrough_frame_classification (v : Fin 4 → Vec3) (hv : IsProjectiveFrame v) :
    Module.finrank ℂ (pencilThrough v) = 2 ∧
      ∃ M : GL3, (pencilThrough v).map (conicPullback M).toLinearMap = standardPencil := by
  obtain ⟨M,c,hc,he⟩ := exists_matrix_of_projectiveFrame v hv
  have hp : pencilThrough v =
      pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i)) := by
    ext Q
    constructor
    · intro hQ i
      change quadraticValue Q ((M : Mat3).mulVec (TetrahedralGroup.diagonal i)) = 0
      rw [he,quadraticValue_smul,hQ,mul_zero]
    · intro hQ i
      have hh := hQ i
      change quadraticValue Q ((M : Mat3).mulVec (TetrahedralGroup.diagonal i)) = 0 at hh
      rw [he,quadraticValue_smul] at hh
      exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 (hc i))
  constructor
  · rw [hp]
    exact finrank_pencilThrough_transformed M
  · exact ⟨M,by rw [hp]; exact pencilThrough_transformed_map M⟩

/-- The stabilizer of the actual standard pencil is exactly scalar multiples
of the frozen tetrahedral group, hence is `Γ` after projectivizing. -/
theorem standard_pencil_stabilizer_iff (M : GL3) :
    pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i)) = standardPencil ↔
      ∃ g : TetrahedralGroup.Gamma, ∃ c : ℂ,
        c ≠ 0 ∧ (M : Mat3) = c • TetrahedralGroup.matrix g := by
  constructor
  · intro hp
    apply (standard_stabilizer_iff M).mp
    intro i
    have hne : (M : Mat3).mulVec (TetrahedralGroup.diagonal i) ≠ 0 := by
      intro hz
      apply TetrahedralGroup.diagonal_ne_zero i
      apply (vectorEquiv M).injective
      simpa using hz
    have hbase : BaseVector standardPencil ((M : Mat3).mulVec (TetrahedralGroup.diagonal i)) := by
      rw [← hp]
      intro Q hQ
      exact hQ i
    have hh := (standard_projective_base_locus _ hne).mp hbase
    exact hh
  · rintro ⟨g,c,hc,hm⟩
    ext Q
    rw [conic_in_standardPencil_iff]
    constructor
    · intro hQ i
      obtain ⟨j,hj⟩ := (TetrahedralGroup.framePermutation g).surjective i
      have hh := hQ j
      change quadraticValue Q ((M : Mat3).mulVec (TetrahedralGroup.diagonal j)) = 0 at hh
      rw [hm,Matrix.smul_mulVec,TetrahedralGroup.matrix_diagonal,smul_smul,
        quadraticValue_smul,hj] at hh
      exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 (mul_ne_zero hc
        (TetrahedralGroup.orientation_ne_zero (TetrahedralGroup.framePermutation g))))
    · intro hQ i
      change quadraticValue Q ((M : Mat3).mulVec (TetrahedralGroup.diagonal i)) = 0
      rw [hm,Matrix.smul_mulVec,TetrahedralGroup.matrix_diagonal,smul_smul,
        quadraticValue_smul,hQ,mul_zero]

/-- Coordinate change transports the entire conic submodule through the actual points. -/
theorem pencilThrough_map_pullback (M : GL3) (v : Fin 4 → Vec3) :
    (pencilThrough v).map (conicPullback M).toLinearMap =
      pencilThrough (fun i => (↑M⁻¹ : Mat3).mulVec (v i)) := by
  ext Q
  constructor
  · rintro ⟨R,hR,rfl⟩ i
    change quadraticValue (conicPullback M R) ((↑M⁻¹ : Mat3).mulVec (v i)) = 0
    rw [quadraticValue_pullback]
    simpa [Matrix.mulVec_mulVec] using hR i
  · intro hQ
    refine ⟨conicPullback M⁻¹ Q,?_,conicPullback_apply_inv M Q⟩
    intro i
    rw [quadraticValue_pullback]
    exact hQ i

/-- The framed pencil represented by a literal `GL₃` matrix. -/
def framedPencil (M : GL3) : Submodule ℂ Conic :=
  pencilThrough (fun i => (M : Mat3).mulVec (TetrahedralGroup.diagonal i))

/-- The fibers of the standard-pencil orbit map are exactly the tetrahedral
right cosets after scalar matrices are removed. -/
theorem framedPencil_fiber_iff (M N : GL3) :
    framedPencil M = framedPencil N ↔
      ∃ g : TetrahedralGroup.Gamma, ∃ c : ℂ,
        c ≠ 0 ∧ (↑(N⁻¹ * M) : Mat3) = c • TetrahedralGroup.matrix g := by
  have hleft : (framedPencil M).map (conicPullback N).toLinearMap = framedPencil (N⁻¹ * M) := by
    rw [framedPencil,pencilThrough_map_pullback,framedPencil]
    congr 1
    funext i
    simp only [Units.val_mul,Matrix.mulVec_mulVec]
  have hright : (framedPencil N).map (conicPullback N).toLinearMap = standardPencil :=
    pencilThrough_transformed_map N
  constructor
  · intro h
    apply (standard_pencil_stabilizer_iff _).mp
    change framedPencil (N⁻¹ * M) = standardPencil
    rw [← hleft,h,hright]
  · intro h
    apply Submodule.map_injective_of_injective (conicPullback N).injective
    rw [hleft,hright]
    exact (standard_pencil_stabilizer_iff _).mpr h

/-- The four-plane displayed in Section 4.1: symmetric matrices with equal diagonal entries. -/
def standardFourPlane : Submodule ℂ Conic where
  carrier := {A | A.val 0 0 = A.val 1 1 ∧ A.val 1 1 = A.val 2 2}
  zero_mem' := by constructor <;> rfl
  add_mem' := by
    intro A B hA hB
    constructor
    · change A.val 0 0 + B.val 0 0 = A.val 1 1 + B.val 1 1
      rw [hA.1,hB.1]
    · change A.val 1 1 + B.val 1 1 = A.val 2 2 + B.val 2 2
      rw [hA.2,hB.2]
  smul_mem' := by
    intro c A hA
    constructor
    · change c * A.val 0 0 = c * A.val 1 1
      rw [hA.1]
    · change c * A.val 1 1 = c * A.val 2 2
      rw [hA.2]

def tracePair (A Q : Conic) : ℂ := Matrix.trace (A.val * Q.val)

theorem tracePair_standardFirst (A : Conic) :
    tracePair A standardFirst = A.val 0 0 - A.val 1 1 := by
  simp [tracePair,standardFirst,diagonalConic,Matrix.trace,Matrix.mul_apply,
    Fin.sum_univ_succ,sub_eq_add_neg]

theorem tracePair_standardSecond (A : Conic) :
    tracePair A standardSecond = A.val 1 1 - A.val 2 2 := by
  simp [tracePair,standardSecond,diagonalConic,Matrix.trace,Matrix.mul_apply,
    Fin.sum_univ_succ,sub_eq_add_neg]

/-- The displayed four-plane is the actual trace-pairing annihilator of the standard pencil. -/
theorem standardFourPlane_annihilator (A : Conic) :
    A ∈ standardFourPlane ↔ ∀ Q ∈ standardPencil, tracePair A Q = 0 := by
  constructor
  · intro hA Q hQ
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hQ
    change Matrix.trace (A.val * (a • standardFirst.val + b • standardSecond.val)) = 0
    rw [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,Matrix.trace_add,
      Matrix.trace_smul,Matrix.trace_smul]
    change a * tracePair A standardFirst + b * tracePair A standardSecond = 0
    rw [tracePair_standardFirst,tracePair_standardSecond,hA.1,hA.2]
    ring
  · intro h
    constructor
    · have hh := h standardFirst (Submodule.subset_span (by simp))
      exact sub_eq_zero.mp ((tracePair_standardFirst A) ▸ hh)
    · have hh := h standardSecond (Submodule.subset_span (by simp))
      exact sub_eq_zero.mp ((tracePair_standardSecond A) ▸ hh)

/-- The four independent coordinates are the common diagonal and three off-diagonal entries. -/
def standardFourPlaneCoordinates : standardFourPlane ≃ₗ[ℂ] (Fin 4 → ℂ) where
  toFun A := ![A.val.val 0 0,A.val.val 0 1,A.val.val 0 2,A.val.val 1 2]
  invFun v := ⟨⟨!![v 0,v 1,v 2;v 1,v 0,v 3;v 2,v 3,v 0],by
    change Matrix.transpose _ = _
    funext i j
    fin_cases i <;> fin_cases j <;> rfl⟩,by constructor <;> rfl⟩
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    have h10 : A.val.val 1 0 = A.val.val 0 1 := congrFun (congrFun A.val.property 0) 1
    have h20 : A.val.val 2 0 = A.val.val 0 2 := congrFun (congrFun A.val.property 0) 2
    have h21 : A.val.val 2 1 = A.val.val 1 2 := congrFun (congrFun A.val.property 1) 2
    have h01 := A.property.1
    have h12 := A.property.2
    funext i j
    fin_cases i <;> fin_cases j <;> simp [h10,h20,h21,h01,h12]
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' A B := by funext i; fin_cases i <;> rfl
  map_smul' c A := by funext i; fin_cases i <;> rfl

theorem finrank_standardFourPlane : Module.finrank ℂ standardFourPlane = 4 := by
  rw [standardFourPlaneCoordinates.finrank_eq]
  simp

/-- The determinant binary cubic of the standard pencil has three distinct
projective zero directions, represented by `(1,0)`, `(0,1)`, and `(1,1)`. -/
theorem det_standard_combination (a b : ℂ) :
    Matrix.det (a • standardFirst + b • standardSecond).val = a * b * (a-b) := by
  rw [Matrix.det_fin_three]
  simp [standardFirst,standardSecond,diagonalConic]
  ring

theorem singular_standard_combination_iff (a b : ℂ) :
    Matrix.det (a • standardFirst + b • standardSecond).val = 0 ↔
      a = 0 ∨ b = 0 ∨ a = b := by
  rw [det_standard_combination]
  simp [mul_eq_zero,sub_eq_zero,or_assoc]

theorem standardPencil_contains_nonsingular :
    ∃ Q ∈ standardPencil, Matrix.det Q.val ≠ 0 := by
  refine ⟨standardFirst + (2 : ℂ) • standardSecond,?_,?_⟩
  · exact Submodule.mem_span_pair.mpr ⟨1,2,by rw [one_smul]⟩
  · have hh : Matrix.det (standardFirst + (2 : ℂ) • standardSecond).val = -2 := by
      calc
        _ = (1 : ℂ) * 2 * (1-2) := by
          simpa only [one_smul] using det_standard_combination 1 2
        _ = -2 := by norm_num
    rw [hh]
    norm_num

end M9.ConicPencilFrames

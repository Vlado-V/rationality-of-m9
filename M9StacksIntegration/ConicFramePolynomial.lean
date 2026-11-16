module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The polynomial quotient matrix of a ternary conic frame

The six coordinates are `(00,11,22,01,02,12)`. The standard four-plane
consists of symmetric matrices with equal diagonal entries. Its quotient is
pulled back by the adjugate congruence, so the resulting matrix is polynomial
in the frame entries and homogeneous of degree four.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.ConicFrame

open scoped BigOperators

variable {R : Type*} [CommRing R]

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R
abbrev Mat6 (R : Type*) := Matrix (Fin 6) (Fin 6) R

def symMatrix (x : Fin 6 → R) : Mat3 R :=
  !![x 0,x 3,x 4;x 3,x 1,x 5;x 4,x 5,x 2]

def symCoordinates (A : Mat3 R) : Fin 6 → R :=
  ![A 0 0,A 1 1,A 2 2,A 0 1,A 0 2,A 1 2]

omit [CommRing R] in
@[simp] theorem symMatrix_transpose (x : Fin 6 → R) : (symMatrix x).transpose = symMatrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [CommRing R] in
@[simp] theorem symCoordinates_symMatrix (x : Fin 6 → R) : symCoordinates (symMatrix x) = x := by
  funext i
  fin_cases i <;> rfl

omit [CommRing R] in
theorem symMatrix_symCoordinates (A : Mat3 R) (hA : A.transpose = A) :
    symMatrix (symCoordinates A) = A := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  have h20 : A 2 0 = A 0 2 := congrFun (congrFun hA 0) 2
  have h21 : A 2 1 = A 1 2 := congrFun (congrFun hA 1) 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMatrix,symCoordinates,h10,h20,h21]

theorem congruence_isSymm (F A : Mat3 R) (hA : A.transpose = A) :
    (F * A * F.transpose).transpose = F * A * F.transpose := by
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hA]
  simp only [Matrix.mul_assoc]

def congruence (F : Mat3 R) : Mat6 R := fun i j =>
  symCoordinates (F * symMatrix (Pi.single j 1) * F.transpose) i

/-- The matrix is the literal coordinate matrix of congruence on symmetric forms. -/
theorem congruence_mulVec (F : Mat3 R) (x : Fin 6 → R) :
    (congruence F).mulVec x = symCoordinates (F * symMatrix x * F.transpose) := by
  funext i
  fin_cases i <;>
    simp [congruence,symCoordinates,symMatrix,Matrix.mulVec,Matrix.mul_apply,
      dotProduct,Matrix.transpose_apply,Fin.sum_univ_succ,Pi.single_apply] <;> ring

@[simp] theorem congruence_one : congruence (1 : Mat3 R) = 1 := by
  ext i j
  simp only [congruence,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one,symCoordinates_symMatrix]
  simp [Matrix.one_apply,Pi.single_apply]

/-- The six-dimensional congruence matrices form an actual representation. -/
theorem congruence_mul (F G : Mat3 R) : congruence (F * G) = congruence F * congruence G := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec,congruence_mulVec,congruence_mulVec,congruence_mulVec,
    symMatrix_symCoordinates _ (congruence_isSymm G _ (symMatrix_transpose _))]
  simp only [Matrix.transpose_mul,Matrix.mul_assoc]

theorem symCoordinates_smul (c : R) (A : Mat3 R) : symCoordinates (c • A) = c • symCoordinates A := by
  funext i
  fin_cases i <;> rfl

theorem congruence_smul (c : R) (F : Mat3 R) : congruence (c • F) = c ^ 2 • congruence F := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.smul_mulVec,congruence_mulVec,congruence_mulVec]
  simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [← pow_two,symCoordinates_smul]

def standardQuotient : Matrix (Fin 2) (Fin 6) R :=
  !![1,-1,0,0,0,0;0,1,-1,0,0,0]

def standardSection : Matrix (Fin 6) (Fin 2) R :=
  !![1,1;0,1;0,0;0,0;0,0;0,0]

@[simp] theorem standardQuotient_section :
    (standardQuotient : Matrix (Fin 2) (Fin 6) R) * (standardSection : Matrix (Fin 6) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardQuotient,standardSection,Matrix.mul_apply,Fin.sum_univ_succ]

theorem standardQuotient_mulVec (x : Fin 6 → R) :
    (standardQuotient : Matrix (Fin 2) (Fin 6) R).mulVec x = ![x 0-x 1,x 1-x 2] := by
  funext i
  fin_cases i <;> simp [standardQuotient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,sub_eq_add_neg]

theorem standardQuotient_kernel (x : Fin 6 → R) :
    (standardQuotient : Matrix (Fin 2) (Fin 6) R).mulVec x = 0 ↔ x 0 = x 1 ∧ x 1 = x 2 := by
  rw [standardQuotient_mulVec]
  constructor
  · intro h
    exact ⟨sub_eq_zero.mp (congrFun h 0),sub_eq_zero.mp (congrFun h 1)⟩
  · rintro ⟨h01,h12⟩
    funext i
    fin_cases i <;> simp [h01,h12]

/-- The actual frame quotient. Its kernel is the transformed standard four-plane. -/
def quotientMatrix (F : Mat3 R) : Matrix (Fin 2) (Fin 6) R :=
  standardQuotient * congruence F.adjugate

@[simp] theorem quotientMatrix_one : quotientMatrix (1 : Mat3 R) = standardQuotient := by
  simp [quotientMatrix,Matrix.adjugate_one]

theorem quotientMatrix_smul (c : R) (F : Mat3 R) :
    quotientMatrix (c • F) = c ^ 4 • quotientMatrix F := by
  rw [quotientMatrix,Matrix.adjugate_smul]
  simp only [Fintype.card_fin,Nat.reduceSub,congruence_smul]
  rw [Matrix.mul_smul]
  congr 1
  ring

/-- The adjugate congruence removes a frame on its image up to the scalar `det(F)²`. -/
theorem quotientMatrix_congruence (F : Mat3 R) :
    quotientMatrix F * congruence F = F.det ^ 2 • standardQuotient := by
  rw [quotientMatrix,Matrix.mul_assoc,← congruence_mul,Matrix.adjugate_mul,congruence_smul,
    congruence_one,Matrix.mul_smul,Matrix.mul_one]

def quotientSection (F : Mat3 R) (hF : IsUnit F.det) : Matrix (Fin 6) (Fin 2) R :=
  (↑hF.unit⁻¹ : R) ^ 2 • (congruence F * standardSection)

/-- The actual quotient has an explicit splitting wherever the frame determinant is a unit. -/
theorem quotientMatrix_section (F : Mat3 R) (hF : IsUnit F.det) :
    quotientMatrix F * quotientSection F hF = 1 := by
  have hunit : (↑hF.unit⁻¹ : R) * F.det = 1 := by
    simpa only [hF.unit_spec] using Units.inv_mul hF.unit
  have hsq : (↑hF.unit⁻¹ : R) ^ 2 * F.det ^ 2 = 1 := by rw [← mul_pow,hunit,one_pow]
  rw [quotientSection,Matrix.mul_smul,← Matrix.mul_assoc,quotientMatrix_congruence,
    Matrix.smul_mul,standardQuotient_section,smul_smul,hsq,one_smul]

theorem quotientMatrix_surjective (F : Mat3 R) (hF : IsUnit F.det) :
    Function.Surjective (quotientMatrix F).mulVec := by
  intro y
  refine ⟨(quotientSection F hF).mulVec y,?_⟩
  rw [Matrix.mulVec_mulVec,quotientMatrix_section,Matrix.one_mulVec]

/-- Congruence by an invertible frame is itself an actual invertible linear matrix. -/
def congruenceUnit (F : Mat3 R) (hF : IsUnit F.det) : (Mat6 R)ˣ where
  val := congruence F
  inv := (↑hF.unit⁻¹ : R) ^ 2 • congruence F.adjugate
  val_inv := by
    have hunit : (↑hF.unit⁻¹ : R) * F.det = 1 := by
      simpa only [hF.unit_spec] using Units.inv_mul hF.unit
    rw [Matrix.mul_smul,← congruence_mul,Matrix.mul_adjugate,congruence_smul,
      congruence_one,smul_smul,← mul_pow,hunit,one_pow,one_smul]
  inv_val := by
    have hunit : (↑hF.unit⁻¹ : R) * F.det = 1 := by
      simpa only [hF.unit_spec] using Units.inv_mul hF.unit
    rw [Matrix.smul_mul,← congruence_mul,Matrix.adjugate_mul,congruence_smul,
      congruence_one,smul_smul,← mul_pow,hunit,one_pow,one_smul]

/-- The kernel is exactly the actual congruence image of the standard four-plane. -/
theorem quotientMatrix_kernel_image (F : Mat3 R) (hF : IsUnit F.det) (y : Fin 6 → R) :
    (quotientMatrix F).mulVec y = 0 ↔
      ∃ x : Fin 6 → R, x 0 = x 1 ∧ x 1 = x 2 ∧ y = (congruence F).mulVec x := by
  constructor
  · intro hy
    let x := (↑(congruenceUnit F hF)⁻¹ : Mat6 R).mulVec y
    have hx : (congruence F).mulVec x = y := by
      change (congruenceUnit F hF : Mat6 R).mulVec
        ((↑(congruenceUnit F hF)⁻¹ : Mat6 R).mulVec y) = y
      rw [Matrix.mulVec_mulVec,Units.mul_inv,Matrix.one_mulVec]
    have hstd : (standardQuotient : Matrix (Fin 2) (Fin 6) R).mulVec x = 0 := by
      have hh := hy
      rw [← hx,Matrix.mulVec_mulVec,quotientMatrix_congruence,Matrix.smul_mulVec] at hh
      have hδ : IsUnit (F.det ^ 2) := hF.pow 2
      exact (hδ.smul_eq_zero.mp hh)
    obtain ⟨h01,h12⟩ := standardQuotient_kernel x |>.mp hstd
    exact ⟨x,h01,h12,hx.symm⟩
  · rintro ⟨x,h01,h12,rfl⟩
    rw [Matrix.mulVec_mulVec,quotientMatrix_congruence,Matrix.smul_mulVec,
      (standardQuotient_kernel x).mpr ⟨h01,h12⟩,smul_zero]

theorem quotientMatrix_kernel_congruence (F A : Mat3 R) (hF : IsUnit F.det)
    (hA : A.transpose = A) :
    (quotientMatrix F).mulVec (symCoordinates A) = 0 ↔
      ∃ S : Mat3 R, S.transpose = S ∧ S 0 0 = S 1 1 ∧ S 1 1 = S 2 2 ∧
        A = F * S * F.transpose := by
  rw [quotientMatrix_kernel_image F hF]
  constructor
  · rintro ⟨x,h01,h12,hx⟩
    refine ⟨symMatrix x,symMatrix_transpose x,h01,h12,?_⟩
    have hh := congrArg symMatrix hx
    rw [symMatrix_symCoordinates A hA,congruence_mulVec,
      symMatrix_symCoordinates _ (congruence_isSymm F _ (symMatrix_transpose x))] at hh
    exact hh
  · rintro ⟨S,hS,h01,h12,hAS⟩
    refine ⟨symCoordinates S,h01,h12,?_⟩
    rw [congruence_mulVec,symMatrix_symCoordinates S hS,hAS]

end M9Native.ConicFrame

module
public import M9StacksIntegration.LagrangianSymmetricCongruence
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.FractionRing

/-! Private compact candidate: triangular factorization of the actual
rank-six congruence representation, followed by universal specialization. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace M9Native.LagrangianSymmetricCongruence

variable (R : Type*) [CommRing R]

private theorem representation_map {S : Type*} [CommRing S] (f : R →+* S)
    (P : Matrix (Fin 3) (Fin 3) R) :
    f.mapMatrix (representation R P) = representation S (f.mapMatrix P) := by
  ext i j
  fin_cases j <;> simp [representation, RingHom.mapMatrix_apply, Matrix.map_apply]

private theorem representation_mul (P Q : Matrix (Fin 3) (Fin 3) R) :
    representation R (P * Q) = representation R P * representation R Q := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  let B := (coordinates R).symm v
  have h := coordinates_congruence R (P * Q) B
  rw [congruence_mul, LinearMap.comp_apply, coordinates_congruence,
    coordinates_congruence] at h
  have hv : coordinates R B = v := (coordinates R).apply_symm_apply v
  rw [hv] at h
  exact h.symm.trans (Matrix.mulVec_mulVec _ _ _)

private theorem det_representation_upper (a b c d e f : R) :
    (representation R !![a,b,c;0,d,e;0,0,f]).det =
      (Matrix.det !![a,b,c;0,d,e;0,0,f]) ^ 4 := by
  have hP : Matrix.IsUpperTriangular !![a,b,c;0,d,e;0,0,f] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hS : (representation R !![a,b,c;0,d,e;0,0,f]).IsUpperTriangular := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [representation, upperPair]
  rw [Matrix.det_of_isUpperTriangular hS, Matrix.det_of_isUpperTriangular hP]
  simp only [Fin.prod_univ_succ, representation, upperPair]
  norm_num
  ring

private theorem det_representation_lower (a b c d e f : R) :
    (representation R !![a,0,0;b,c,0;d,e,f]).det =
      (Matrix.det !![a,0,0;b,c,0;d,e,f]) ^ 4 := by
  have hP : Matrix.IsLowerTriangular !![a,0,0;b,c,0;d,e,f] := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> simp_all
  have hS : (representation R !![a,0,0;b,c,0;d,e,f]).IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> simp_all [representation, upperPair]
  rw [Matrix.det_of_isLowerTriangular _ hS, Matrix.det_of_isLowerTriangular _ hP]
  simp only [Fin.prod_univ_succ, representation, upperPair]
  norm_num
  ring

private theorem det_representation_field {F : Type*} [Field F]
    (P : Matrix (Fin 3) (Fin 3) F) (ha : P 0 0 ≠ 0)
    (hp : P 1 1 - P 1 0 * P 0 1 / P 0 0 ≠ 0) :
    (representation F P).det = P.det ^ 4 := by
  let p := P 1 1 - P 1 0 * P 0 1 / P 0 0
  let q := P 2 1 - P 2 0 * P 0 1 / P 0 0
  let L : Matrix (Fin 3) (Fin 3) F :=
    !![1,0,0;P 1 0 / P 0 0,1,0;P 2 0 / P 0 0,q / p,1]
  let U : Matrix (Fin 3) (Fin 3) F :=
    !![P 0 0,P 0 1,P 0 2;0,p,P 1 2 - P 1 0 * P 0 2 / P 0 0;
      0,0,P 2 2 - P 2 0 * P 0 2 / P 0 0 - q / p * (P 1 2 - P 1 0 * P 0 2 / P 0 0)]
  have hp' : p ≠ 0 := hp
  have hLU : L * U = P := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp (config := { zeta := false })
      [L, U, Matrix.mul_apply, Fin.sum_univ_succ, ha, hp']
    all_goals try dsimp only [p, q]
    all_goals ring
  rw [← hLU, representation_mul, Matrix.det_mul,
    det_representation_lower, det_representation_upper, Matrix.det_mul, mul_pow]

private abbrev UniversalRing := MvPolynomial (Fin 3 × Fin 3) ℤ

private def universalMatrix : Matrix (Fin 3) (Fin 3) UniversalRing :=
  fun i j => MvPolynomial.X (i, j)

private theorem universal_pivot_ne_zero :
    universalMatrix 0 0 ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval₂Hom (RingHom.id ℤ)
    (fun ij : Fin 3 × Fin 3 => if ij.1 = ij.2 then 1 else 0)) h
  norm_num [universalMatrix] at hh

private theorem universal_minor_ne_zero :
    universalMatrix 0 0 * universalMatrix 1 1 -
      universalMatrix 1 0 * universalMatrix 0 1 ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval₂Hom (RingHom.id ℤ)
    (fun ij : Fin 3 × Fin 3 => if ij.1 = ij.2 then 1 else 0)) h
  norm_num [universalMatrix] at hh

private theorem det_representation_universal :
    (representation UniversalRing universalMatrix).det = universalMatrix.det ^ 4 := by
  let f := algebraMap UniversalRing (FractionRing UniversalRing)
  have hf := IsFractionRing.injective UniversalRing (FractionRing UniversalRing)
  have ha : (f.mapMatrix universalMatrix) 0 0 ≠ 0 := by
    intro h
    apply universal_pivot_ne_zero
    apply hf
    exact h.trans f.map_zero.symm
  have hm : (f.mapMatrix universalMatrix) 0 0 * (f.mapMatrix universalMatrix) 1 1 -
      (f.mapMatrix universalMatrix) 1 0 * (f.mapMatrix universalMatrix) 0 1 ≠ 0 := by
    intro h
    apply universal_minor_ne_zero
    apply hf
    simpa only [map_sub, map_mul, map_zero, RingHom.mapMatrix_apply, Matrix.map_apply] using h
  have hp : (f.mapMatrix universalMatrix) 1 1 -
      (f.mapMatrix universalMatrix) 1 0 * (f.mapMatrix universalMatrix) 0 1 /
        (f.mapMatrix universalMatrix) 0 0 ≠ 0 := by
    intro h
    apply hm
    have hh := congrArg (fun x => x * (f.mapMatrix universalMatrix) 0 0) h
    field_simp [ha] at hh
    linear_combination hh
  apply hf
  rw [map_pow, RingHom.map_det, RingHom.map_det, representation_map]
  exact det_representation_field (f.mapMatrix universalMatrix) ha hp

/-- The determinant character of the actual symmetric congruence map. -/
theorem det_representation (P : Matrix (Fin 3) (Fin 3) R) :
    (representation R P).det=P.det^4 := by
  let f : UniversalRing →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ij => P ij.1 ij.2)
  have hP : f.mapMatrix universalMatrix = P := by
    ext i j
    simp [universalMatrix, f, RingHom.mapMatrix_apply, Matrix.map_apply]
  have h := congrArg f det_representation_universal
  simpa only [map_pow, RingHom.map_det, representation_map, hP] using h

end M9Native.LagrangianSymmetricCongruence

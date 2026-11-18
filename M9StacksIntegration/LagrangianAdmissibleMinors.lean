module

public import M9StacksIntegration.LagrangianRingCoordinates
public import M9StacksIntegration.LagrangianSymplecticMatrix
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# An admissible invertible minor of an actual isotropic three-row quotient

The mixed minors are literal column-replacement determinants. Their
symmetry follows from actual row isotropy, and their principal cofactor
relations are universal polynomial identities. An explicit Cauchy–Binet
identity supplies the full-rank contradiction when all eight admissible
minors vanish.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

open Matrix
open scoped BigOperators

universe u

namespace M9Native.LagrangianAdmissibleMinors

abbrev Choice := Fin 3 → Bool

theorem card_choice : Fintype.card Choice=8 := by decide

def column (s : Choice) (i : Fin 3) : Fin 6 :=
  if s i then Fin.natAdd 3 i else i.castAdd 3

theorem column_injective (s : Choice) : Function.Injective (column s) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  unfold column at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd,Fin.val_castAdd] at hv <;> omega

def embedding (s : Choice) : Fin 3 ↪ Fin 6 := ⟨column s,column_injective s⟩

variable {R : Type u} [CommRing R]

def leftBlock (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => M i (j.castAdd 3)

def rightBlock (M : Matrix (Fin 3) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => M i (Fin.natAdd 3 j)

def mixed (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => (A.updateCol i (B.col j)).det

def pairing (A B : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : R :=
  ∑ k : Fin 3,(A i k*B j k-B i k*A j k)

theorem pairing_swap (A B : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    pairing B A i j= -pairing A B i j := by
  simp only [pairing,Fin.sum_univ_succ]
  ring

theorem mixed_skew01 (A B : Matrix (Fin 3) (Fin 3) R) :
    mixed A B 0 1-mixed A B 1 0=
      -(A 2 2*pairing A B 0 1-A 1 2*pairing A B 0 2+A 0 2*pairing A B 1 2) := by
  simp [mixed,pairing,Matrix.det_fin_three,Matrix.updateCol,Matrix.col_apply,Fin.sum_univ_succ]
  ring

theorem mixed_skew02 (A B : Matrix (Fin 3) (Fin 3) R) :
    mixed A B 0 2-mixed A B 2 0=
      A 2 1*pairing A B 0 1-A 1 1*pairing A B 0 2+A 0 1*pairing A B 1 2 := by
  simp [mixed,pairing,Matrix.det_fin_three,Matrix.updateCol,Matrix.col_apply,Fin.sum_univ_succ]
  ring

theorem mixed_skew12 (A B : Matrix (Fin 3) (Fin 3) R) :
    mixed A B 1 2-mixed A B 2 1=
      -(A 2 0*pairing A B 0 1-A 1 0*pairing A B 0 2+A 0 0*pairing A B 1 2) := by
  simp [mixed,pairing,Matrix.det_fin_three,Matrix.updateCol,Matrix.col_apply,Fin.sum_univ_succ]
  ring

theorem mixed_symmetric (A B : Matrix (Fin 3) (Fin 3) R)
    (h : ∀ i j,pairing A B i j=0) (i j : Fin 3) : mixed A B i j=mixed A B j i := by
  have h01 : mixed A B 0 1=mixed A B 1 0 := sub_eq_zero.mp (by rw [mixed_skew01,h 0 1,h 0 2,h 1 2]; simp)
  have h02 : mixed A B 0 2=mixed A B 2 0 := sub_eq_zero.mp (by rw [mixed_skew02,h 0 1,h 0 2,h 1 2]; simp)
  have h12 : mixed A B 1 2=mixed A B 2 1 := sub_eq_zero.mp (by rw [mixed_skew12,h 0 1,h 0 2,h 1 2]; simp)
  fin_cases i <;> fin_cases j
  all_goals first | rfl | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h12 | exact h12.symm

theorem cofactor00 (A B : Matrix (Fin 3) (Fin 3) R) :
    A.det*mixed B A 0 0=mixed A B 1 1*mixed A B 2 2-mixed A B 1 2*mixed A B 2 1 := by
  simp [mixed,Matrix.det_fin_three,Matrix.updateCol,Matrix.col_apply]
  ring

theorem cofactor11 (A B : Matrix (Fin 3) (Fin 3) R) :
    A.det*mixed B A 1 1=mixed A B 0 0*mixed A B 2 2-mixed A B 0 2*mixed A B 2 0 := by
  simp [mixed,Matrix.det_fin_three,Matrix.updateCol,Matrix.col_apply]
  ring

theorem cofactor22 (A B : Matrix (Fin 3) (Fin 3) R) :
    A.det*mixed B A 2 2=mixed A B 0 0*mixed A B 1 1-mixed A B 0 1*mixed A B 1 0 := by
  simp [mixed,Matrix.det_fin_three,Matrix.updateCol,Matrix.col_apply]
  ring

def rowMinor (S : Matrix (Fin 6) (Fin 3) R) (a b c : Fin 6) : R :=
  (S.submatrix ![a,b,c] id).det

private theorem mixed_eq_adjugate_mul (A B : Matrix (Fin 3) (Fin 3) R) :
    mixed A B = A.adjugate * B := by
  ext i j
  change Matrix.cramer A (B.col j) i = (A.adjugate * B) i j
  have h := congrFun (Matrix.cramer_eq_adjugate_mulVec A (B.col j)) i
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.col_apply] using h

private theorem det_add_three (A B : Matrix (Fin 3) (Fin 3) R) :
    (A + B).det = A.det + B.det + (A.adjugate * B).trace + (B.adjugate * A).trace := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace,
    Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

private theorem trace_four_cycle (A B C D : Matrix (Fin 3) (Fin 3) R) :
    ((A * B) * (C * D)).trace = ((B * C) * (D * A)).trace := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  congr 1
  simp only [Matrix.mul_assoc]

private theorem trace_mul_three (A C : Matrix (Fin 3) (Fin 3) R) :
    (A * C).trace = ∑ j : Fin 3, (A 0 j * C j 0 + A 1 j * C j 1 + A 2 j * C j 2) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private def topRows (S : Matrix (Fin 6) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => S (i.castAdd 3) j

private def bottomRows (S : Matrix (Fin 6) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => S (Fin.natAdd 3 i) j

private theorem topRows_det (S : Matrix (Fin 6) (Fin 3) R) :
    (topRows S).det = rowMinor S 0 1 2 := by
  apply congrArg Matrix.det
  ext i j
  fin_cases i <;> rfl

private theorem bottomRows_det (S : Matrix (Fin 6) (Fin 3) R) :
    (bottomRows S).det = rowMinor S 3 4 5 := by
  apply congrArg Matrix.det
  ext i j
  fin_cases i <;> rfl

private theorem top_row_coefficient (S : Matrix (Fin 6) (Fin 3) R) (j i : Fin 3) :
    (bottomRows S * (topRows S).adjugate) j i =
      ![rowMinor S 1 2 (Fin.natAdd 3 j), -rowMinor S 0 2 (Fin.natAdd 3 j),
        rowMinor S 0 1 (Fin.natAdd 3 j)] i := by
  fin_cases i <;>
    simp [topRows, bottomRows, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_succ, rowMinor, Matrix.det_fin_three] <;> ring

private theorem bottom_row_coefficient (S : Matrix (Fin 6) (Fin 3) R) (j i : Fin 3) :
    (topRows S * (bottomRows S).adjugate) j i =
      ![rowMinor S (j.castAdd 3) 4 5, -rowMinor S (j.castAdd 3) 3 5,
        rowMinor S (j.castAdd 3) 3 4] i := by
  fin_cases i <;>
    simp [topRows, bottomRows, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_succ, rowMinor, Matrix.det_fin_three] <;> ring

private theorem mul_eq_block_sum (M : Matrix (Fin 3) (Fin 6) R)
    (S : Matrix (Fin 6) (Fin 3) R) :
    M * S = leftBlock M * topRows S + rightBlock M * bottomRows S := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, leftBlock, rightBlock, topRows, bottomRows]
  exact Fin.sum_univ_add (fun k : Fin (3 + 3) => M i k * S k j)

/-- The literal twenty-term Cauchy–Binet identity, without a choice of a minor. -/
theorem det_mul_expansion (M : Matrix (Fin 3) (Fin 6) R) (S : Matrix (Fin 6) (Fin 3) R) :
    (M*S).det=(leftBlock M).det*rowMinor S 0 1 2+(rightBlock M).det*rowMinor S 3 4 5+
      ∑ j : Fin 3, (
        mixed (leftBlock M) (rightBlock M) 0 j*rowMinor S 1 2 (Fin.natAdd 3 j)-
        mixed (leftBlock M) (rightBlock M) 1 j*rowMinor S 0 2 (Fin.natAdd 3 j)+
        mixed (leftBlock M) (rightBlock M) 2 j*rowMinor S 0 1 (Fin.natAdd 3 j)+
        mixed (rightBlock M) (leftBlock M) 0 j*rowMinor S (j.castAdd 3) 4 5-
        mixed (rightBlock M) (leftBlock M) 1 j*rowMinor S (j.castAdd 3) 3 5+
        mixed (rightBlock M) (leftBlock M) 2 j*rowMinor S (j.castAdd 3) 3 4) := by
  rw [mul_eq_block_sum, det_add_three, Matrix.det_mul, Matrix.det_mul,
    Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    trace_four_cycle (topRows S).adjugate (leftBlock M).adjugate (rightBlock M) (bottomRows S),
    trace_four_cycle (bottomRows S).adjugate (rightBlock M).adjugate (leftBlock M) (topRows S),
    ← mixed_eq_adjugate_mul (leftBlock M) (rightBlock M),
    ← mixed_eq_adjugate_mul (rightBlock M) (leftBlock M),
    trace_mul_three, trace_mul_three, topRows_det, bottomRows_det]
  simp only [top_row_coefficient, bottom_row_coefficient, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Fin.sum_univ_succ]
  ring

def admissibleMinor (M : Matrix (Fin 3) (Fin 6) R) (s : Choice) : R :=
  (M.submatrix id (embedding s)).det

theorem minor_false (M : Matrix (Fin 3) (Fin 6) R) :
    admissibleMinor M (fun _ => false)=(leftBlock M).det := rfl

theorem minor_true (M : Matrix (Fin 3) (Fin 6) R) :
    admissibleMinor M (fun _ => true)=(rightBlock M).det := rfl

theorem minor_single_true (M : Matrix (Fin 3) (Fin 6) R) (k : Fin 3) :
    admissibleMinor M (fun i => decide (i=k))=mixed (leftBlock M) (rightBlock M) k k := by
  unfold admissibleMinor mixed
  apply congrArg Matrix.det
  ext i j
  by_cases h : j=k
  · subst j
    simp [Matrix.submatrix_apply,embedding,column,Matrix.updateCol,Matrix.col_apply,rightBlock]
  · simp [Matrix.submatrix_apply,embedding,column,Matrix.updateCol,Matrix.col_apply,leftBlock,rightBlock,h]

theorem minor_single_false (M : Matrix (Fin 3) (Fin 6) R) (k : Fin 3) :
    admissibleMinor M (fun i => decide (i≠k))=mixed (rightBlock M) (leftBlock M) k k := by
  unfold admissibleMinor mixed
  apply congrArg Matrix.det
  ext i j
  by_cases h : j=k
  · subst j
    simp [Matrix.submatrix_apply,embedding,column,Matrix.updateCol,Matrix.col_apply,leftBlock]
  · simp [Matrix.submatrix_apply,embedding,column,Matrix.updateCol,Matrix.col_apply,leftBlock,rightBlock,h]

section Field
variable {K : Type u} [Field K]

theorem mixed_zero_of_diagonal_zero (A B : Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j,pairing A B i j=0) (hu : A.det=0) (hd : ∀ i,mixed A B i i=0) :
    ∀ i j,mixed A B i j=0 := by
  have hs := mixed_symmetric A B h
  have hp01 : mixed A B 0 1*mixed A B 1 0=0 := by
    have hp := cofactor22 A B
    rw [hu,hd 0,hd 1] at hp
    simpa only [zero_mul,zero_sub,neg_eq_zero] using hp.symm
  have hp02 : mixed A B 0 2*mixed A B 2 0=0 := by
    have hp := cofactor11 A B
    rw [hu,hd 0,hd 2] at hp
    simpa only [zero_mul,zero_sub,neg_eq_zero] using hp.symm
  have hp12 : mixed A B 1 2*mixed A B 2 1=0 := by
    have hp := cofactor00 A B
    rw [hu,hd 1,hd 2] at hp
    simpa only [zero_mul,zero_sub,neg_eq_zero] using hp.symm
  rw [hs 1 0] at hp01
  rw [hs 2 0] at hp02
  rw [hs 2 1] at hp12
  have h01 : mixed A B 0 1=0 := mul_self_eq_zero.mp hp01
  have h02 : mixed A B 0 2=0 := mul_self_eq_zero.mp hp02
  have h12 : mixed A B 1 2=0 := mul_self_eq_zero.mp hp12
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first | exact hd _ | exact h01 | exact h02 | exact h12 |
    exact (hs _ _).trans h01 | exact (hs _ _).trans h02 | exact (hs _ _).trans h12

/-- A genuine full-row-rank isotropic three-by-six field matrix has an
actual invertible minor choosing one coordinate from each symplectic pair. -/
theorem exists_isUnit_admissibleMinor (M : Matrix (Fin 3) (Fin 6) K)
    (hsurj : Function.Surjective M.mulVec)
    (hiso : ∀ i j,M9Native.LagrangianRing.omega K (M i) (M j)=0) :
    ∃ s : Choice,IsUnit (admissibleMinor M s) := by
  classical
  by_contra hnone
  have hzero (s : Choice) : admissibleMinor M s=0 := by
    by_contra hz
    exact hnone ⟨s,isUnit_iff_ne_zero.mpr hz⟩
  have hu : (leftBlock M).det=0 := (minor_false M).symm.trans (hzero _)
  have hz : (rightBlock M).det=0 := (minor_true M).symm.trans (hzero _)
  have hxd (i : Fin 3) : mixed (leftBlock M) (rightBlock M) i i=0 :=
    (minor_single_true M i).symm.trans (hzero _)
  have hyd (i : Fin 3) : mixed (rightBlock M) (leftBlock M) i i=0 :=
    (minor_single_false M i).symm.trans (hzero _)
  have hp (i j : Fin 3) : pairing (leftBlock M) (rightBlock M) i j=0 := by
    simpa only [pairing,leftBlock,rightBlock,M9Native.LagrangianRing.omega_apply,
      M9Native.LagrangianRing.omegaValue,M9Native.LagrangianRing.eIndex,
      M9Native.LagrangianRing.fIndex] using hiso i j
  have hp' (i j : Fin 3) : pairing (rightBlock M) (leftBlock M) i j=0 := by
    rw [pairing_swap,hp,neg_zero]
  have hx := mixed_zero_of_diagonal_zero (leftBlock M) (rightBlock M) hp hu hxd
  have hy := mixed_zero_of_diagonal_zero (rightBlock M) (leftBlock M) hp' hz hyd
  obtain ⟨S,hMS⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
  have hc := det_mul_expansion M S
  rw [hMS,Matrix.det_one] at hc
  simp only [hu,hz,hx,hy,zero_mul,add_zero,sub_zero,Finset.sum_const_zero] at hc
  exact one_ne_zero hc

end Field

end M9Native.LagrangianAdmissibleMinors

end

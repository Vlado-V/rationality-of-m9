module

public import M9StacksIntegration.MovingConicCells
public import M9StacksIntegration.ConicFrameSourceMatrix

/-! The actual moving conic cell is the negative nonpivot block of the
actual normalized quotient matrix. This identifies the actual moving frame
base with the native Grassmannian chart coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

open Matrix
open scoped Classical

namespace M9Native.ConicMovingBaseCoordinates

open M9.GraphBundleDescent M9.MovingDeterminantFrames
open M9.DeterminantFrameScalarExtension
open ConicCompatibleGraphCoordinates ConicFrameHeadMatrices MovingConicCells

variable (K : Type*) [Field K] [Algebra ℂ K]

omit [Algebra ℂ K] in
theorem conicCoordinates_split (q : M9.Symmetric3 K) :
    conicCoordinates K q = Fin.append (conicSplit K q).2 (conicSplit K q).1 := by
  funext i
  fin_cases i <;> rfl

theorem quotient_kills_moving (F : GL3 K) (q : movingPlane K (standardPlane K) F) :
    (ConicFrame.quotientMatrix F.val).mulVec (conicCoordinates K q.val) = 0 := by
  obtain ⟨r,hr,hq⟩ := q.property
  have he : r ∈ equalDiagonalPlane K := by
    rw [← standardPlane_eq_equalDiagonal K]
    exact hr
  have hd := (mem_equalDiagonalPlane K r).mp he
  apply (ConicFrame.quotientMatrix_kernel_image F.val
    (Matrix.GeneralLinearGroup.det F).isUnit (conicCoordinates K q.val)).mpr
  refine ⟨conicCoordinates K r,hd.1,hd.2,?_⟩
  rw [ConicFrame.congruence_mulVec]
  change ConicFrame.symCoordinates q.val.val =
    ConicFrame.symCoordinates (F.val * ConicFrame.symMatrix (ConicFrame.symCoordinates r.val) * F.val.transpose)
  rw [ConicFrame.symMatrix_symCoordinates r.val r.property]
  exact congrArg (fun v : M9.Symmetric3 K => conicCoordinates K v) hq.symm

def normalizedQuotient (F : GL3 K) : Matrix (Fin 2) (Fin 6) K :=
  ((ConicFrame.quotientMatrix F.val).submatrix id (Fin.castAdd 4))⁻¹ *
    ConicFrame.quotientMatrix F.val

omit [Algebra ℂ K] in
theorem normalizedQuotient_pivots (F : GL3 K)
    (hP : IsUnit ((ConicFrame.quotientMatrix F.val).submatrix id (Fin.castAdd 4)).det) :
    (normalizedQuotient K F).submatrix id (Fin.castAdd 4) = 1 := by
  rw [normalizedQuotient, Matrix.submatrix_mul _ _ id id (Fin.castAdd 4)
    Function.bijective_id, Matrix.submatrix_id_id, Matrix.nonsing_inv_mul _ hP]

theorem normalizedQuotient_kills_cell (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (x : Head K) :
    (normalizedQuotient K F).mulVec (Fin.append ((movingCellMatrix K F hR).mulVec x) x) = 0 := by
  let q := movingCellFrame K F hR ((standardPlaneBasis K).equivFun.symm x)
  have hc : conicSplit K q.val = (x,(movingCellMatrix K F hR).mulVec x) :=
    (movingCellFrame_coordinates K F hR ((standardPlaneBasis K).equivFun.symm x)).trans
      (congrArg (fun y => (y,(movingCellMatrix K F hR).mulVec y))
        ((standardPlaneBasis K).equivFun.apply_symm_apply x))
  have he : conicCoordinates K q.val = Fin.append ((movingCellMatrix K F hR).mulVec x) x :=
    (conicCoordinates_split K q.val).trans (congrArg (fun z : Head K × Tail K => Fin.append z.2 z.1) hc)
  have hk := quotient_kills_moving K F q
  have hn : (normalizedQuotient K F).mulVec (conicCoordinates K q.val) = 0 := by
    change (((ConicFrame.quotientMatrix F.val).submatrix id (Fin.castAdd 4))⁻¹ *
      ConicFrame.quotientMatrix F.val).mulVec _ = 0
    rw [← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]
  exact (congrArg (normalizedQuotient K F).mulVec he).symm.trans hn

omit [Algebra ℂ K] in
theorem mulVec_append (Q : Matrix (Fin 2) (Fin 6) K) (u : Tail K) (v : Head K) :
    Q.mulVec (Fin.append u v) =
      (Q.submatrix id (Fin.castAdd 4)).mulVec u +
        (Q.submatrix id (Fin.natAdd 2)).mulVec v := by
  funext i
  change (∑ j : Fin (2+4), Q i j * Fin.append u v j) =
    (∑ j : Fin 2, Q i (Fin.castAdd 4 j) * u j) +
      (∑ j : Fin 4, Q i (Fin.natAdd 2 j) * v j)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

omit [Algebra ℂ K] in
theorem normalized_kills_cell_coordinates (Q : Matrix (Fin 2) (Fin 6) K) (A : BaseMatrix K)
    (hP : Q.submatrix id (Fin.castAdd 4) = 1)
    (hQ : ∀ x : Head K, Q.mulVec (Fin.append (A.mulVec x) x) = 0)
    (i : Fin 2) (j : Fin 4) : Q i (Fin.natAdd 2 j) = - A i j := by
  have h := (mulVec_append K Q (A.mulVec (Pi.single j 1)) (Pi.single j 1)).symm.trans
    (hQ (Pi.single j 1))
  rw [hP, Matrix.one_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  have hi := congrFun h i
  exact eq_neg_iff_add_eq_zero.mpr (by
    simpa only [Pi.add_apply, Pi.zero_apply, Matrix.col_apply, Matrix.submatrix_apply,
      id_eq, add_comm] using hi)

/-- The exact quotient/kernel coordinate identity for the genuine moving
plane, with both required minors named explicitly. -/
theorem normalizedQuotient_nonpivot (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (hP : IsUnit ((ConicFrame.quotientMatrix F.val).submatrix id (Fin.castAdd 4)).det)
    (i : Fin 2) (j : Fin 4) :
    normalizedQuotient K F i (Fin.natAdd 2 j) = - movingCellMatrix K F hR i j :=
  normalized_kills_cell_coordinates K (normalizedQuotient K F) (movingCellMatrix K F hR)
    (normalizedQuotient_pivots K F hP) (normalizedQuotient_kills_cell K F hR) i j

end M9Native.ConicMovingBaseCoordinates

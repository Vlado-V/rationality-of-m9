module

public import M9StacksIntegration.ConicFrameHeadMatrices

/-! Actual moving conic four-planes in the native head/tail big cell. The
cell frame is an explicit linear equivalence built from the original moving
frame and the proved invertible head matrix. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Matrix

namespace M9Native.MovingConicCells

open ConicCompatibleGraphCoordinates ConicFrameHeadMatrices M9.GraphBundleDescent
open M9.DeterminantFrameScalarExtension M9.MovingDeterminantFrames

variable (K : Type*) [Field K] [Algebra ℂ K]

def headUnit (F : GL3 K) (hR : IsUnit (headMatrix K F).det) : Matrix.GeneralLinearGroup (Fin 4) K :=
  Matrix.GeneralLinearGroup.mk'' (headMatrix K F) hR

def headChange (F : GL3 K) (hR : IsUnit (headMatrix K F).det) : Head K ≃ₗ[K] Head K :=
  matrixLinearEquiv K (headUnit K F hR)

def standardEndo (F : GL3 K) (hR : IsUnit (headMatrix K F).det) : standardPlane K ≃ₗ[K] standardPlane K :=
  (standardPlaneBasis K).equivFun.trans ((headChange K F hR).trans (standardPlaneBasis K).equivFun.symm)

def movingCellMatrix (F : GL3 K) (hR : IsUnit (headMatrix K F).det) : BaseMatrix K :=
  tailMatrix K F * (headUnit K F hR)⁻¹.val

/-- An actual frame of the original moving plane, whose head is the original
standard-plane coordinate. -/
def movingCellFrame (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    standardPlane K ≃ₗ[K] movingPlane K (standardPlane K) F :=
  (standardEndo K F hR).symm.trans (movingFrame K (standardPlane K) F)

theorem head_formula (F : GL3 K) (q : standardPlane K) :
    (conicSplit K (congruenceEquiv K F q.val)).1 =
      (headMatrix K F).mulVec ((standardPlaneBasis K).equivFun q) := by
  have h := congrArg (fun f : Head K →ₗ[K] Head K => f ((standardPlaneBasis K).equivFun q))
    (Matrix.toLin'_toMatrix' (headLinear K F))
  change (headMatrix K F).mulVec ((standardPlaneBasis K).equivFun q) =
    (conicSplit K (congruenceEquiv K F
      ((standardPlaneBasis K).equivFun.symm ((standardPlaneBasis K).equivFun q)).val)).1 at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem tail_formula (F : GL3 K) (q : standardPlane K) :
    (conicSplit K (congruenceEquiv K F q.val)).2 =
      (tailMatrix K F).mulVec ((standardPlaneBasis K).equivFun q) := by
  have h := congrArg (fun f : Head K →ₗ[K] Tail K => f ((standardPlaneBasis K).equivFun q))
    (Matrix.toLin'_toMatrix' (tailLinear K F))
  change (tailMatrix K F).mulVec ((standardPlaneBasis K).equivFun q) =
    (conicSplit K (congruenceEquiv K F
      ((standardPlaneBasis K).equivFun.symm ((standardPlaneBasis K).equivFun q)).val)).2 at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem headChange_symm (F : GL3 K) (hR : IsUnit (headMatrix K F).det) (v : Head K) :
    (headChange K F hR).symm v = (headUnit K F hR)⁻¹.val.mulVec v := by
  have h := congrArg (fun e : Head K ≃ₗ[K] Head K => e v)
    ((matrixLinearEquiv K).map_inv (headUnit K F hR))
  exact h.symm

theorem standardEndo_symm_coordinates (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (q : standardPlane K) :
    (standardPlaneBasis K).equivFun ((standardEndo K F hR).symm q) =
      (headUnit K F hR)⁻¹.val.mulVec ((standardPlaneBasis K).equivFun q) := by
  change (standardPlaneBasis K).equivFun ((standardPlaneBasis K).equivFun.symm
    ((headChange K F hR).symm ((standardPlaneBasis K).equivFun q))) = _
  rw [LinearEquiv.apply_symm_apply, headChange_symm]

/-- Exact actual graph-cell coordinates of the original moving frame. -/
theorem movingCellFrame_coordinates (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (q : standardPlane K) :
    conicSplit K (movingCellFrame K F hR q).val =
      ((standardPlaneBasis K).equivFun q,
        (movingCellMatrix K F hR).mulVec ((standardPlaneBasis K).equivFun q)) := by
  change conicSplit K (congruenceEquiv K F ((standardEndo K F hR).symm q).val) = _
  apply Prod.ext
  · rw [head_formula, standardEndo_symm_coordinates]
    change (headUnit K F hR).val.mulVec
      ((headUnit K F hR)⁻¹.val.mulVec ((standardPlaneBasis K).equivFun q)) = _
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rw [tail_formula, standardEndo_symm_coordinates, Matrix.mulVec_mulVec]
    rfl

/-- Equality of genuine submodules, derived from the explicit frame. -/
theorem movingPlane_eq_cell (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    (movingPlane K (standardPlane K) F).map (conicSplit K).toLinearMap =
      cell K (movingCellMatrix K F hR) := by
  apply le_antisymm
  · rintro y ⟨v,hv,rfl⟩
    obtain ⟨q,hq⟩ := (movingCellFrame K F hR).surjective ⟨v,hv⟩
    have hqv := congrArg Subtype.val hq
    change (movingCellFrame K F hR q).val = v at hqv
    change conicSplit K v ∈ cell K (movingCellMatrix K F hR)
    rw [← hqv, movingCellFrame_coordinates, mem_cell]
  · intro y hy
    have htail := (mem_cell K (movingCellMatrix K F hR) y).mp hy
    let q := (standardPlaneBasis K).equivFun.symm y.1
    refine ⟨(movingCellFrame K F hR q).val, (movingCellFrame K F hR q).property, ?_⟩
    change conicSplit K (movingCellFrame K F hR q).val = y
    rw [movingCellFrame_coordinates]
    change ((standardPlaneBasis K).equivFun ((standardPlaneBasis K).equivFun.symm y.1),
      (movingCellMatrix K F hR).mulVec
        ((standardPlaneBasis K).equivFun ((standardPlaneBasis K).equivFun.symm y.1))) = y
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl htail.symm

/-- The original moving frame and actual cell frame differ by the literal
head endomorphism of the original standard four-plane. -/
theorem movingFrame_comparison (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    (movingFrame K (standardPlane K) F).trans (movingCellFrame K F hR).symm =
      standardEndo K F hR := by
  apply LinearEquiv.ext
  intro q
  change standardEndo K F hR ((movingFrame K (standardPlane K) F).symm
    (movingFrame K (standardPlane K) F q)) = _
  rw [LinearEquiv.symm_apply_apply]

end M9Native.MovingConicCells

module

public import M9StacksIntegration.MukaiProjectiveKernelCoordinates

/-! # Actual twenty-minor functionals and dual-basis coordinates -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.MukaiPluckerKernelPoint

open Module M9Native.MukaiProjectiveKernelCoordinates

variable (K : Type u) [Field K]

def minorFunctional (M : Matrix (Fin 2) (Fin 5) K) : Module.Dual K (Forms K) :=
  Module.Dual.eval K (Coordinates K)
    (MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1))

theorem eval_reindexed_dualBasis {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (e : I ≃ Fin (n+1)) (w : I → K) (t : Fin (n+1)) :
    Module.Dual.eval K (I → K) w ((Pi.basisFun K I).dualBasis.reindex e t) = w (e.symm t) := by
  simp

theorem orderedMinors_pivot (ι : MukaiOrderedMinors.OrderedPair)
    (M : Matrix (Fin 2) (Fin 5) K) (hM : M.submatrix id ι = 1) :
    MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1) ι = 1 := by
  rw [MukaiOrderedMinors.orderedMinorCoordinates_eq_det,hM,Matrix.det_one]

theorem orderedMinors_ne_zero (ι : MukaiOrderedMinors.OrderedPair)
    (M : Matrix (Fin 2) (Fin 5) K) (hM : M.submatrix id ι = 1) :
    MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1) ≠ 0 := by
  intro hz
  have h := congrFun hz ι
  rw [orderedMinors_pivot K ι M hM,Pi.zero_apply] at h
  exact one_ne_zero h

end M9Native.MukaiPluckerKernelPoint

module

public import M9StacksIntegration.MukaiQuarticCoordinates

/-!
# Structural block-volume rules for the actual exterior cubic

Four vectors in the three-dimensional last block force the alternating
volume to vanish. A volume with three vectors in each block is the
product of their literal three-dimensional determinants. These rules
avoid expanding large tables of six-dimensional permutation signs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

namespace M9Native.MukaiQuarticBlockVolume

open LagrangianField MukaiQuarticExterior MukaiQuarticCoordinates

variable (K : Type*) [Field K]

theorem signature_zero_of_four_last (a : Fin 6 → Fin 6) (s : Fin 4 ↪ Fin 6)
    (v : Fin 4 → Fin 3) (h : ∀ i, a (s i) = fIndex (v i)) : signature K a = 0 := by
  have hn : ¬ Function.Injective a := by
    intro ha
    have hv : Function.Injective v := by
      intro i j hij
      apply s.injective
      apply ha
      rw [h i, h j, hij]
    have hc := Fintype.card_le_of_injective v hv
    norm_num at hc
  simp only [signature, ite_eq_right hn]

def blockMatrix (a : Fin 3 → Fin 3) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of (fun i j => if i = a j then 1 else 0)

def epsilon (a b c : Fin 3) : K := (blockMatrix K ![a,b,c]).det

theorem epsilon_missing (a b : Fin 3) :
    epsilon K a (nextOne b) (nextTwo b) = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [epsilon, blockMatrix, Matrix.det_fin_three, nextOne, nextTwo]

theorem volume_blocks (a b : Fin 3 → Fin 3) :
    volume K (exteriorPower.ιMulti K 6
      (Fin.append (fun i => e K (a i)) (fun i => f K (b i)))) =
      (blockMatrix K a).det * (blockMatrix K b).det := by
  rw [volume_ιMulti, Basis.det_apply]
  have hright (u v : Fin 3 → V K) (j : Fin 3) : Fin.append u v (j.addNat 3) = v j := by
    have hj : j.addNat 3 = Fin.natAdd 3 j := Fin.ext (Nat.add_comm j.val 3)
    rw [hj, Fin.append_right]
  have h : (Pi.basisFun K (Fin 6)).toMatrix
      (Fin.append (fun i => e K (a i)) (fun i => f K (b i))) =
      (Matrix.fromBlocks (blockMatrix K a) 0 0 (blockMatrix K b)).submatrix
        (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm
        (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm := by
    ext i j
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).surjective i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).surjective j
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    cases i <;> cases j <;>
      simp [Basis.toMatrix_apply, blockMatrix, e, f, basisVector, eIndex, fIndex,
        Pi.single_apply, finSumFinEquiv_apply_left (m := 3) (n := 3),
        finSumFinEquiv_apply_right (m := 3) (n := 3),
        Fin.append_left (m := 3) (n := 3), hright, Fin.ext_iff] <;> omega
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

end M9Native.MukaiQuarticBlockVolume

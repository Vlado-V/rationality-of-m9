module

public import M9StacksIntegration.MukaiQuarticBlockVolume

/-! Structural signs of actual exterior block volumes. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiQuarticBlockSigns

open LagrangianField MukaiQuarticExterior MukaiQuarticCoordinates MukaiQuarticBlockVolume

variable (K : Type*) [Field K]

theorem signature_perm (a : Fin 6 → Fin 6) (s : Equiv.Perm (Fin 6)) :
    signature K (a ∘ s) = s.sign • signature K a := by
  rw [← volume_signature, ← volume_signature, volume_ιMulti, volume_ιMulti]
  exact (Pi.basisFun K (Fin 6)).det.map_perm (fun i => basisVector K (a i)) s

theorem signature_F1245 (x y : Fin 6) (a b c d : Fin 3) :
    signature K ![x,fIndex a,fIndex b,y,fIndex c,fIndex d] = 0 := by
  refine signature_zero_of_four_last K _ ⟨![1,2,4,5], by decide⟩ ![a,b,c,d] ?_
  intro i
  fin_cases i <;> rfl

theorem signature_F0245 (x y : Fin 6) (a b c d : Fin 3) :
    signature K ![fIndex a,x,fIndex b,y,fIndex c,fIndex d] = 0 := by
  refine signature_zero_of_four_last K _ ⟨![0,2,4,5], by decide⟩ ![a,b,c,d] ?_
  intro i
  fin_cases i <;> rfl

theorem signature_F0123 (x y : Fin 6) (a b c d : Fin 3) :
    signature K ![fIndex a,fIndex b,fIndex c,fIndex d,x,y] = 0 := by
  refine signature_zero_of_four_last K _ ⟨![0,1,2,3], by decide⟩ ![a,b,c,d] ?_
  intro i
  fin_cases i <;> rfl

theorem signature_F0145 (x y : Fin 6) (a b c d : Fin 3) :
    signature K ![fIndex a,fIndex b,x,y,fIndex c,fIndex d] = 0 := by
  refine signature_zero_of_four_last K _ ⟨![0,1,4,5], by decide⟩ ![a,b,c,d] ?_
  intro i
  fin_cases i <;> rfl

theorem signature_F0345 (x y : Fin 6) (a b c d : Fin 3) :
    signature K ![fIndex a,x,y,fIndex b,fIndex c,fIndex d] = 0 := by
  refine signature_zero_of_four_last K _ ⟨![0,3,4,5], by decide⟩ ![a,b,c,d] ?_
  intro i
  fin_cases i <;> rfl

theorem signature_F2345 (x y : Fin 6) (a b c d : Fin 3) :
    signature K ![x,y,fIndex a,fIndex b,fIndex c,fIndex d] = 0 := by
  refine signature_zero_of_four_last K _ ⟨![2,3,4,5], by decide⟩ ![a,b,c,d] ?_
  intro i
  fin_cases i <;> rfl

theorem signature_eeefff (a b c d e f : Fin 3) :
    signature K ![eIndex a,eIndex b,eIndex c,fIndex d,fIndex e,fIndex f] =
      epsilon K a b c * epsilon K d e f := by
  rw [← volume_signature]
  have h : (fun i : Fin 6 => basisVector K
      (![eIndex a,eIndex b,eIndex c,fIndex d,fIndex e,fIndex f] i)) =
      Fin.append (fun i => LagrangianField.e K (![a,b,c] i))
        (fun i => LagrangianField.f K (![d,e,f] i)) := by
    funext i
    fin_cases i <;> rfl
  rw [h, volume_blocks]
  rfl

theorem signature_eefeff (a b c d e f : Fin 3) :
    signature K ![eIndex a,eIndex b,fIndex d,eIndex c,fIndex e,fIndex f] =
      -(epsilon K a b c * epsilon K d e f) := by
  have h : ![eIndex a,eIndex b,fIndex d,eIndex c,fIndex e,fIndex f] =
      ![eIndex a,eIndex b,eIndex c,fIndex d,fIndex e,fIndex f] ∘
        Equiv.swap (2 : Fin 6) 3 := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [h, signature_perm, Equiv.Perm.sign_swap (by decide), signature_eeefff]
  simp

theorem signature_fffeee (a b c d e f : Fin 3) :
    signature K ![fIndex d,fIndex e,fIndex f,eIndex a,eIndex b,eIndex c] =
      -(epsilon K a b c * epsilon K d e f) := by
  let s : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5
  have h : ![fIndex d,fIndex e,fIndex f,eIndex a,eIndex b,eIndex c] =
      ![eIndex a,eIndex b,eIndex c,fIndex d,fIndex e,fIndex f] ∘ s := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  rw [h, signature_perm, signature_eeefff]
  simp [s, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem signature_feeeff (a b c d e f : Fin 3) :
    signature K ![fIndex d,eIndex a,eIndex b,eIndex c,fIndex e,fIndex f] =
      -(epsilon K a b c * epsilon K d e f) := by
  let s : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1
  have h : ![fIndex d,eIndex a,eIndex b,eIndex c,fIndex e,fIndex f] =
      ![eIndex a,eIndex b,eIndex c,fIndex d,fIndex e,fIndex f] ∘ s := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  rw [h, signature_perm, signature_eeefff]
  simp [s, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem epsilon_missing_last (a b : Fin 3) :
    epsilon K (nextOne b) (nextTwo b) a = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [epsilon, blockMatrix, Matrix.det_fin_three, nextOne, nextTwo]

theorem epsilon_interior (b j d : Fin 3) :
    (if j = nextOne b then (1 : K) else 0) * (if nextTwo b = d then 1 else 0) -
      (if j = nextTwo b then 1 else 0) * (if nextOne b = d then 1 else 0) =
      epsilon K b j d := by
  fin_cases b <;> fin_cases j <;> fin_cases d <;>
    norm_num [epsilon, blockMatrix, Matrix.det_fin_three, nextOne, nextTwo]

end M9Native.MukaiQuarticBlockSigns

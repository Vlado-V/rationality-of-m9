module

public import M9StacksIntegration.MukaiPrimitiveProjector
public import M9StacksIntegration.MukaiQuarticCubic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Coordinate computation rules for the genuine exterior cubic

These are actual determinant-volume formulas for the actual operator.
The integral determinant on the right of `volume_basis` permits finite
coordinate calculations without adding a computational axiom.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiQuarticCoordinates

open LagrangianField MukaiQuarticExterior MukaiQuarticHitchin
open MukaiQuarticCubic MukaiPrimitiveProjector

variable (K : Type*) [Field K]

theorem volume_basis (a : Fin 6 → Fin 6) :
    volume K (exteriorPower.ιMulti K 6 (fun i => basisVector K (a i))) =
      (Int.castRingHom K) (Matrix.det (Matrix.of
        (fun i j : Fin 6 => if a j = i then (1 : ℤ) else 0))) := by
  rw [volume_ιMulti, Basis.det_apply]
  have h : (Pi.basisFun K (Fin 6)).toMatrix (fun i => basisVector K (a i)) =
      (Matrix.of (fun i j : Fin 6 => if a j = i then (1 : ℤ) else 0)).map (Int.castRingHom K) := by
    ext i j
    simp [Basis.toMatrix_apply, basisVector, Pi.single_apply, Matrix.map_apply, eq_comm]
  rw [h, RingHom.map_det]
  rfl

theorem volume_standard :
    volume K (exteriorPower.ιMulti K 6 (fun i => basisVector K i)) = 1 := by
  rw [volume_basis]
  have h : Matrix.of (fun i j : Fin 6 => if j = i then (1 : ℤ) else 0) =
      (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
    ext i j
    simp [Matrix.one_apply, eq_comm]
  rw [h, Matrix.det_one, map_one]

theorem volume_basis_compute (a : Fin 6 → Fin 6) :
    volume K (exteriorPower.ιMulti K 6 (fun i => basisVector K (a i))) =
      if Function.Injective a then
        (∏ j : Fin 6, ∏ i : Fin 6,
          if i < j then (if a i < a j then (1 : ℤˣ) else -1) else 1) • (1 : K)
      else 0 := by
  by_cases ha : Function.Injective a
  · rw [ite_eq_left ha, volume_ιMulti]
    let s : Equiv.Perm (Fin 6) := Equiv.ofBijective a ⟨ha, Finite.surjective_of_injective ha⟩
    have hs : s.sign = ∏ j : Fin 6, ∏ i : Fin 6,
        if i < j then (if a i < a j then (1 : ℤˣ) else -1) else 1 := by
      rw [s.sign_eq_prod_prod_Iio]
      apply Finset.prod_congr rfl
      intro j _
      rw [show Finset.Iio j = Finset.univ.filter (fun i : Fin 6 => i < j) from by
        ext i; simp, Finset.prod_filter]
      rfl
    have hfun : (fun i => basisVector K (a i)) = (Pi.basisFun K (Fin 6)) ∘ s := by
      funext i
      dsimp only [Function.comp_apply]
      rw [Pi.basisFun_apply]
      simp only [s]
      rfl
    rw [hfun, AlternatingMap.map_perm, Basis.det_self, hs]
  · rw [ite_eq_right ha, volume_ιMulti]
    apply AlternatingMap.map_eq_zero_of_not_injective
    intro h
    apply ha
    intro i j hij
    apply h
    exact congrArg (basisVector K) hij

theorem volume_opposite_blocks :
    volume K (exteriorPower.ιMulti K 6
      (fun i => basisVector K (![3,4,5,0,1,2] i))) = -1 := by
  rw [volume_basis_compute]
  norm_num [Function.Injective, Fin.forall_fin_succ, Fin.prod_univ_succ]

theorem mixedOperator_ιMulti (u v : Fin 3 → V K) (φ : DualSix K) (x : V K) :
    mixedOperator K (exteriorPower.ιMulti K 3 u) (exteriorPower.ιMulti K 3 v) φ x =
      φ (u 0) * volume K (exteriorPower.ιMulti K 6
        (Fin.append (Fin.append (fun _ : Fin 1 => x) ![u 1,u 2]) v)) -
      φ (u 1) * volume K (exteriorPower.ιMulti K 6
        (Fin.append (Fin.append (fun _ : Fin 1 => x) ![u 0,u 2]) v)) +
      φ (u 2) * volume K (exteriorPower.ιMulti K 6
        (Fin.append (Fin.append (fun _ : Fin 1 => x) ![u 0,u 1]) v)) := by
  rw [mixedOperator_apply]
  simp only [mixedTop, interior_ιMulti, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [one_ιMulti]
  have h (a b : V K) : wedge2 K a b = exteriorPower.ιMulti K 2 ![a,b] := rfl
  simp only [h, wedgeMul_ιMulti]

def signature (a : Fin 6 → Fin 6) : K :=
  if Function.Injective a then
    (∏ j : Fin 6, ∏ i : Fin 6,
      if i < j then (if a i < a j then (1 : ℤˣ) else -1) else 1) • (1 : K)
  else 0

theorem volume_signature (a : Fin 6 → Fin 6) :
    volume K (exteriorPower.ιMulti K 6 (fun i => basisVector K (a i))) = signature K a :=
  volume_basis_compute K a

theorem volume_six_basis (i a b c d e : Fin 6) :
    volume K (exteriorPower.ιMulti K 6 (Fin.append
      (Fin.append (fun _ : Fin 1 => basisVector K i) ![basisVector K a,basisVector K b])
      ![basisVector K c,basisVector K d,basisVector K e])) =
      signature K ![i,a,b,c,d,e] := by
  have h : Fin.append
      (Fin.append (fun _ : Fin 1 => basisVector K i) ![basisVector K a,basisVector K b])
      ![basisVector K c,basisVector K d,basisVector K e] =
      fun j => basisVector K (![i,a,b,c,d,e] j) := by
    funext j
    fin_cases j <;> rfl
  rw [h, volume_signature]

theorem mixedOperator_basis (a b c d e f i j : Fin 6) :
    mixedOperator K (wedge3 K (basisVector K a) (basisVector K b) (basisVector K c))
      (wedge3 K (basisVector K d) (basisVector K e) (basisVector K f))
      (LinearMap.proj j) (basisVector K i) =
      (if j = a then 1 else 0) * signature K ![i,b,c,d,e,f] -
      (if j = b then 1 else 0) * signature K ![i,a,c,d,e,f] +
      (if j = c then 1 else 0) * signature K ![i,a,b,d,e,f] := by
  simp only [wedge3, mixedOperator_ιMulti, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [volume_six_basis, volume_six_basis, volume_six_basis]
  simp only [LinearMap.proj_apply, basisVector, Pi.single_apply]

end M9Native.MukaiQuarticCoordinates

module

public import M9StacksIntegration.MukaiPrimitiveProjector
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Tactic

/-!
# An independent triple defines a nonzero original primitive hyperplane

The actual Plücker quadratic relation excludes every nonzero sigma-wedge
from the decomposable cone. The checked primitive projector therefore
shows that an independent triple has nonzero class in the actual dual
primitive module. Its fourteen coefficients use the original native
primitive basis, with no substituted hyperplane model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Module Matrix exteriorPower
open scoped BigOperators

universe u

namespace M9Native.PrimitiveDecomposableNonzero

open LagrangianField MukaiPrimitiveDuality MukaiConormalPrimitive MukaiPrimitiveProjector

variable (K : Type u) [Field K]

/-- The original ordered exterior-coordinate functional; repeated indices are allowed. -/
def coordinate (a b c : Fin 6) : Third K →ₗ[K] K :=
  exteriorPower.pairingDual K (V K) 3
    (exteriorPower.ιMulti K 3 ![LinearMap.proj a, LinearMap.proj b, LinearMap.proj c])

/-- Its actual decomposable value is the literal three-by-three minor. -/
theorem coordinate_ιMulti (v : Fin 3 → V K) (a b c : Fin 6) :
    coordinate K a b c (exteriorPower.ιMulti K 3 v) =
      (Matrix.of fun i j : Fin 3 => v i (![a,b,c] j)).det := by
  rw [coordinate, exteriorPower.pairingDual_ιMulti_ιMulti]
  congr 1
  ext i j
  fin_cases j <;> rfl

/-- The original common-index Plücker quadratic. -/
def relation (w : Third K) (a b c d e : Fin 6) : K :=
  coordinate K a b c w * coordinate K a d e w -
    coordinate K a b d w * coordinate K a c e w +
      coordinate K a b e w * coordinate K a c d w

/-- This genuine Plücker relation holds for every actual decomposable third wedge. -/
theorem relation_ιMulti (v : Fin 3 → V K) (a b c d e : Fin 6) :
    relation K (exteriorPower.ιMulti K 3 v) a b c d e = 0 := by
  simp only [relation, coordinate_ιMulti, Matrix.det_fin_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Actual sigma-wedge coordinate evaluation, inherited from the original coefficient pairing. -/
theorem coordinate_wedgeSigma (v : V K) (a b c : Fin 6) :
    coordinate K a b c (wedgeSigma K v) =
      vectorDuality K v
        (contraction K (wedge3 K (basisVector K a) (basisVector K b) (basisVector K c))) :=
  wedgeSigma_coordinate K a b c v

/-- A Plücker quadratic of a sigma-wedge is the square of its original e-coordinate. -/
theorem relation_wedgeSigma_e (v : V K) (i : Fin 3) :
    relation K (wedgeSigma K v) (eIndex i)
      (eIndex (nextOne i)) (fIndex (nextOne i))
      (eIndex (nextTwo i)) (fIndex (nextTwo i)) = (v (eIndex i)) ^ 2 := by
  simp only [relation, coordinate_wedgeSigma, contraction_wedge3,
    map_add, map_sub, map_smul, vectorDuality_apply]
  fin_cases i <;>
    simp [nextOne, nextTwo, omega_apply, omegaValue, basisVector,
      eIndex, fIndex, Fin.sum_univ_succ, Pi.single_apply, smul_eq_mul, pow_two]

/-- The other three original coordinates are detected by the same genuine quadrics. -/
theorem relation_wedgeSigma_f (v : V K) (i : Fin 3) :
    relation K (wedgeSigma K v) (fIndex i)
      (eIndex (nextOne i)) (fIndex (nextOne i))
      (eIndex (nextTwo i)) (fIndex (nextTwo i)) = (v (fIndex i)) ^ 2 := by
  simp only [relation, coordinate_wedgeSigma, contraction_wedge3,
    map_add, map_sub, map_smul, vectorDuality_apply]
  fin_cases i <;>
    simp [nextOne, nextTwo, omega_apply, omegaValue, basisVector,
      eIndex, fIndex, Fin.sum_univ_succ, Pi.single_apply, smul_eq_mul, pow_two]

/-- No nonzero actual sigma-wedge is decomposable. This uses only actual Plücker relations. -/
theorem eq_zero_of_wedgeSigma_eq_ιMulti (v : V K) (s : Fin 3 → V K)
    (h : wedgeSigma K v = exteriorPower.ιMulti K 3 s) : v = 0 := by
  have he (i : Fin 3) : v (eIndex i) = 0 := by
    have hp := relation_ιMulti K s (eIndex i)
      (eIndex (nextOne i)) (fIndex (nextOne i))
      (eIndex (nextTwo i)) (fIndex (nextTwo i))
    rw [← h, relation_wedgeSigma_e] at hp
    exact sq_eq_zero_iff.mp hp
  have hf (i : Fin 3) : v (fIndex i) = 0 := by
    have hp := relation_ιMulti K s (fIndex i)
      (eIndex (nextOne i)) (fIndex (nextOne i))
      (eIndex (nextTwo i)) (fIndex (nextTwo i))
    rw [← h, relation_wedgeSigma_f] at hp
    exact sq_eq_zero_iff.mp hp
  funext j
  fin_cases j
  · exact he 0
  · exact he 1
  · exact he 2
  · exact hf 0
  · exact hf 1
  · exact hf 2

/-- An independent original triple has nonzero actual exterior product. -/
theorem ιMulti_ne_zero (s : Fin 3 → V K) (hs : LinearIndependent K s) :
    exteriorPower.ιMulti K 3 s ≠ 0 := by
  let t : Set.powersetCard (Fin 3) 3 :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono (id : Fin 3 → Fin 3) strictMono_id)
  have hli := exteriorPower.ιMulti_family_linearIndependent_field (n := 3) hs
  have hn := LinearIndependent.ne_zero t hli
  simpa [t, exteriorPower.ιMulti_family] using hn

variable [CharZero K]

/-- The actual native primitive quotient cannot kill an independent decomposable triple. -/
theorem primitiveClass_ιMulti_ne_zero (s : Fin 3 → V K) (hs : LinearIndependent K s) :
    primitiveClass K (exteriorPower.ιMulti K 3 s) ≠ 0 := by
  intro hz
  let w := exteriorPower.ιMulti K 3 s
  have hp : projector K w = 0 :=
    (representative_primitiveClass K w).symm.trans
      ((congrArg (representative K) hz).trans (map_zero _))
  have hw : w = wedgeSigma K ((2 : K)⁻¹ • contraction K w) := by
    have h : w - (2 : K)⁻¹ • wedgeSigma K (contraction K w) = 0 := hp
    exact (sub_eq_zero.mp h).trans (map_smul (wedgeSigma K) (2 : K)⁻¹ (contraction K w)).symm
  have hv := eq_zero_of_wedgeSigma_eq_ιMulti K _ s hw.symm
  exact ιMulti_ne_zero K s hs (hw.trans (by rw [hv, map_zero]))

/-- The literal original fourteen hyperplane coefficients of the original triple. -/
def coefficients (s : Fin 3 → V K) : Fin 14 → K := fun j =>
  primitiveClass K (exteriorPower.ιMulti K 3 s) (LagrangianPluckerLinear.primitiveBasis14 K j)

/-- These actual native coefficients are nonzero for every independent original triple. -/
theorem coefficients_ne_zero (s : Fin 3 → V K) (hs : LinearIndependent K s) :
    coefficients K s ≠ 0 := by
  intro hz
  apply primitiveClass_ιMulti_ne_zero K s hs
  apply (LagrangianPluckerLinear.primitiveBasis14 K).ext
  intro j
  exact congrArg (fun v : Fin 14 → K => v j) hz

end M9Native.PrimitiveDecomposableNonzero

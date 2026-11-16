module

public import M9StacksIntegration.MukaiConormalOriginCoordinates
public import M9StacksIntegration.LagrangianCoordinateFieldChange
public import M9StacksIntegration.LagrangianPluckerFirstJet

/-! The actual fourteen projected row coefficients over every coefficient
ring, with the original finite coordinate reindexing preserved. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

universe u

namespace M9Native.MukaiConormalRowCoordinates

open LagrangianField hiding coordinate nextOne nextTwo aCoordinate bCoordinate qCoordinate pCoordinate
open LagrangianPluckerFirstJet

variable (K : Type u) [Field K]

theorem basis14_coordinates (r : Coordinates K) (j : Fin 14) :
    (coordinateBasis14 K).equivFun r j =
      match LagrangianCoordinateFieldChange.coordinateIndexEquiv.symm j with
      | .inl _ => r.1
      | .inr (.inl ij) => r.2.1.val ij.val.1 ij.val.2
      | .inr (.inr (.inl ij)) => r.2.2.1.val ij.val.1 ij.val.2
      | .inr (.inr (.inr _)) => r.2.2.2 := by
  change (coordinateBasis K).repr r
    (LagrangianCoordinateFieldChange.coordinateIndexEquiv.symm j) = _
  generalize LagrangianCoordinateFieldChange.coordinateIndexEquiv.symm j = x
  rcases x with x | x
  · simp [coordinateBasis]
  · rcases x with ij | x
    · simp [coordinateBasis]
      rfl
    · rcases x with ij | x
      · simp [coordinateBasis]
        rfl
      · simp [coordinateBasis]

section CoefficientRing

variable {R : Type u} [CommRing R] (κ : K →+* R)

theorem coordinate_basis_map (a b c : Fin 6) (j : Fin 20) :
    κ (coordinate K a b c (LagrangianRing.thirdBasis20 K j)) =
      coordinate R a b c (LagrangianRing.thirdBasis20 R j) := by
  rw [LagrangianRing.thirdBasis20_apply, LagrangianRing.thirdBasis20_apply]
  simp only [coordinate, exteriorPower.pairingDual_ιMulti_ιMulti]
  rw [RingHom.map_det]
  congr 1
  ext i k
  have hf (p : Prop) [Decidable p] (a b : K) :
      κ (if p then a else b) = if p then κ a else κ b := by split_ifs <;> rfl
  fin_cases i <;> fin_cases k <;> simp [LagrangianRing.basisVector, Pi.single_apply, hf]

theorem coordinate_eq_sum (a b c : Fin 6) (w : LagrangianRing.Third R) :
    coordinate R a b c w = ∑ j : Fin 20,
      (LagrangianRing.thirdBasis20 R).equivFun w j *
        coordinate R a b c (LagrangianRing.thirdBasis20 R j) := by
  have h := congrArg (coordinate R a b c) ((LagrangianRing.thirdBasis20 R).sum_repr w)
  simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.equivFun_apply] using h.symm

theorem extraction_sum (a b c : Fin 6) (M : Matrix (Fin 3) (Fin 6) R) :
    (∑ j : Fin 20, κ (coordinate K a b c (LagrangianRing.thirdBasis20 K j)) *
      LagrangianRing.rowTwenty R M j) = coordinate R a b c (LagrangianRing.rowPlucker R M) := by
  calc
    _ = ∑ j : Fin 20, LagrangianRing.rowTwenty R M j *
        coordinate R a b c (LagrangianRing.thirdBasis20 R j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [coordinate_basis_map K κ]
      exact mul_comm _ _
    _ = _ := (coordinate_eq_sum (R := R) a b c _).symm

theorem rowFourteen_extraction (M : Matrix (Fin 3) (Fin 6) R) (j : Fin 14) :
    LagrangianRing.rowFourteen R κ M j =
      match LagrangianCoordinateFieldChange.coordinateIndexEquiv.symm j with
      | .inl _ => aCoordinate R (LagrangianRing.rowPlucker R M)
      | .inr (.inl ij) => qCoordinate R ij.val.1 ij.val.2 (LagrangianRing.rowPlucker R M)
      | .inr (.inr (.inl ij)) => pCoordinate R ij.val.1 ij.val.2 (LagrangianRing.rowPlucker R M)
      | .inr (.inr (.inr _)) => bCoordinate R (LagrangianRing.rowPlucker R M) := by
  simp only [LagrangianRing.rowFourteen, Matrix.mulVec_apply_eq_sum, Matrix.map_apply,
    LagrangianCoordinateFieldChange.projectionMatrix_apply]
  generalize LagrangianCoordinateFieldChange.coordinateIndexEquiv.symm j = x
  rcases x with x | x
  · exact extraction_sum K κ 0 1 2 M
  · rcases x with ij | x
    · exact extraction_sum K κ (ij.val.1.castAdd 3)
        (Fin.natAdd 3 (nextOne ij.val.2)) (Fin.natAdd 3 (nextTwo ij.val.2)) M
    · rcases x with ij | x
      · exact extraction_sum K κ (Fin.natAdd 3 ij.val.1)
          ((nextOne ij.val.2).castAdd 3) ((nextTwo ij.val.2).castAdd 3) M
      · exact extraction_sum K κ 3 4 5 M

theorem rowFourteen_standard_pivot (A : Matrix (Fin 3) (Fin 3) R) :
    LagrangianRing.rowFourteen R κ (standard R A)
      MukaiConormalOriginCoordinates.originPivot = 1 := by
  have hi : LagrangianCoordinateFieldChange.coordinateIndexEquiv.symm
      MukaiConormalOriginCoordinates.originPivot = .inl () := by
    change MukaiConormalOriginCoordinates.coordinateIndexEquiv.symm
      (MukaiConormalOriginCoordinates.coordinateIndexEquiv (.inl ())) = _
    exact Equiv.symm_apply_apply _ _
  rw [rowFourteen_extraction, hi]
  exact aCoordinate_standard R A

end CoefficientRing

theorem rowFourteen_standard_firstJet (B : Symmetric3 K) (j : Fin 14) :
    (LagrangianRing.rowFourteen (DualNumber K) (algebraMap K (DualNumber K))
      (standard (DualNumber K) (LagrangianInfinitesimal.firstOrderMatrix K 0 B.val)) j).snd =
      (coordinateBasis14 K).equivFun (0,0,B,0) j := by
  rw [rowFourteen_extraction, basis14_coordinates]
  generalize LagrangianCoordinateFieldChange.coordinateIndexEquiv.symm j = x
  rcases x with x | x
  · exact firstJet_a K 0 B.val
  · rcases x with ij | x
    · exact firstJet_q_zero K B.val ij.val.1 ij.val.2
    · rcases x with ij | x
      · exact (firstJet_p K 0 B.val ij.val.1 ij.val.2).trans
          (congrFun (congrFun B.property ij.val.1) ij.val.2)
      · exact firstJet_b_zero K B.val

end M9Native.MukaiConormalRowCoordinates

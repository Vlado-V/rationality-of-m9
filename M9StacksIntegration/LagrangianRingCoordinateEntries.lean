module

public import M9StacksIntegration.LagrangianCoordinateBasisEntries

/-! Original primitive coordinate entries after arbitrary coefficient-ring
extension.  The finite reindex is the actual frozen coordinateBasis14. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

universe u

namespace M9Native.LagrangianRingCoordinateEntries

def extraction (R : Type u) [CommRing R] :
    LagrangianField.CoordinateIndex → LagrangianRing.Third R →ₗ[R] R :=
  Sum.elim (fun _ => LagrangianPluckerFirstJet.aCoordinate R)
    (Sum.elim (fun ij => LagrangianPluckerFirstJet.qCoordinate R ij.val.1 ij.val.2)
      (Sum.elim (fun ij => LagrangianPluckerFirstJet.pCoordinate R ij.val.1 ij.val.2)
        (fun _ => LagrangianPluckerFirstJet.bCoordinate R)))

theorem extraction_field (K : Type u) [Field K] (i : LagrangianField.CoordinateIndex) :
    extraction K i = LagrangianCoordinateBasisEntries.extraction K i := by
  cases i with
  | inl i => rfl
  | inr i =>
    cases i with
    | inl ij => rfl
    | inr i => cases i <;> rfl

theorem coordinate_basis_map {K R : Type u} [CommRing K] [CommRing R]
    (κ : K →+* R) (a b c : Fin 6) (j : Fin 20) :
    κ (LagrangianPluckerFirstJet.coordinate K a b c (LagrangianRing.thirdBasis20 K j)) =
      LagrangianPluckerFirstJet.coordinate R a b c (LagrangianRing.thirdBasis20 R j) := by
  rw [LagrangianRing.thirdBasis20_apply, LagrangianRing.thirdBasis20_apply]
  simp only [LagrangianPluckerFirstJet.coordinate, exteriorPower.pairingDual_ιMulti_ιMulti]
  rw [RingHom.map_det]
  congr 1
  funext i k
  fin_cases i <;> fin_cases k <;>
    simp [LagrangianRing.basisVector, Pi.single_apply, apply_ite] <;>
      split_ifs <;> simp_all

theorem extraction_basis_map {K R : Type u} [Field K] [CommRing R]
    (κ : K →+* R) (i : LagrangianField.CoordinateIndex) (j : Fin 20) :
    κ (LagrangianCoordinateBasisEntries.extraction K i (LagrangianField.thirdBasis20 K j)) =
      extraction R i (LagrangianRing.thirdBasis20 R j) := by
  rw [← extraction_field, ← LagrangianRing.thirdBasis20_eq_field K]
  cases i with
  | inl i =>
    simpa only [extraction, Sum.elim_inl, LagrangianPluckerFirstJet.aCoordinate] using
      coordinate_basis_map κ 0 1 2 j
  | inr i =>
    cases i with
    | inl ij =>
      simpa only [extraction, Sum.elim_inr, Sum.elim_inl, LagrangianPluckerFirstJet.qCoordinate] using
        coordinate_basis_map κ (ij.val.1.castAdd 3)
          (Fin.natAdd 3 (LagrangianPluckerFirstJet.nextOne ij.val.2))
          (Fin.natAdd 3 (LagrangianPluckerFirstJet.nextTwo ij.val.2)) j
    | inr i =>
      cases i with
      | inl ij =>
        simpa only [extraction, Sum.elim_inr, Sum.elim_inl, LagrangianPluckerFirstJet.pCoordinate] using
          coordinate_basis_map κ (Fin.natAdd 3 ij.val.1)
            ((LagrangianPluckerFirstJet.nextOne ij.val.2).castAdd 3)
            ((LagrangianPluckerFirstJet.nextTwo ij.val.2).castAdd 3) j
      | inr i =>
        simpa only [extraction, Sum.elim_inr, LagrangianPluckerFirstJet.bCoordinate] using
          coordinate_basis_map κ 3 4 5 j

theorem extraction_sum_basis (R : Type u) [CommRing R] (i : LagrangianField.CoordinateIndex)
    (w : LagrangianRing.Third R) :
    extraction R i w = ∑ j : Fin 20,
      extraction R i (LagrangianRing.thirdBasis20 R j) * (LagrangianRing.thirdBasis20 R).repr w j := by
  have h := congrArg (extraction R i) ((LagrangianRing.thirdBasis20 R).sum_repr w)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h.symm

/-- The actual original fourteen coordinates are the original cyclic
minor entries after every coefficient-ring extension, including nilpotents. -/
theorem rowFourteen_entry {K R : Type u} [Field K] [CommRing R] (κ : K →+* R)
    (M : Matrix (Fin 3) (Fin 6) R) (i : LagrangianField.CoordinateIndex) :
    LagrangianRing.rowFourteen R κ M (LagrangianCoordinateBasisEntries.indexEquiv i) =
      extraction R i (LagrangianRing.rowPlucker R M) := by
  simp only [LagrangianRing.rowFourteen, Matrix.mulVec_apply, dotProduct, Matrix.row_apply, Matrix.map_apply,
    LagrangianCoordinateBasisEntries.projectionMatrix_entry, extraction_basis_map]
  simpa only [LagrangianRing.rowTwenty, Basis.equivFun_apply] using
    (extraction_sum_basis R i (LagrangianRing.rowPlucker R M)).symm

end M9Native.LagrangianRingCoordinateEntries

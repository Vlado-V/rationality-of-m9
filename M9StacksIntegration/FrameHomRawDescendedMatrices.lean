module

public import M9StacksIntegration.FrameHomRawMatrixCoordinates
public import M9StacksIntegration.FrameHomRawOddCoordinates
public import Mathlib.LinearAlgebra.Matrix.Basis

/-! Actual raw/descended change-of-basis matrices on the original Hom
function field. The universal invariant coordinates are R^-1 X L,
with L and R derived from the genuine scalar-extended descended bases.
The original tensor exchange proves R = sigma(L). -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Module
open scoped Classical BigOperators

namespace M9Native.FrameHomRawDescendedMatrices

open M9.FrameBundleDescent M9.FrameBundleDescent.Standard
open M9.FrameHomFieldDescent M9.DeterminantFrameScalarExtension
open FrameHomRawMatrixCoordinates

def basisChange {V : Type*} [AddCommGroup V] [Module Ambient V]
    (b₀ b₁ : Basis (Fin 4) Ambient V) : Matrix.GeneralLinearGroup (Fin 4) Ambient where
  val := b₀.toMatrix b₁
  inv := b₁.toMatrix b₀
  val_inv := b₀.toMatrix_mul_toMatrix_flip b₁
  inv_val := b₁.toMatrix_mul_toMatrix_flip b₀

/-- Columns are the actual descended source basis in literal raw coordinates. -/
def leftChange : Matrix.GeneralLinearGroup (Fin 4) Ambient :=
  basisChange (rawBasis false) leftRawBasis

/-- Columns are the actual descended target basis in literal raw coordinates. -/
def rightChange : Matrix.GeneralLinearGroup (Fin 4) Ambient :=
  basisChange (rawBasis true) rightRawBasis

theorem leftChange_entry (i j : Fin 4) :
    leftChange.val i j = rawCoordinates Ambient (leftRawBasis j) i :=
  rawBasis_repr false _ _

theorem rightChange_entry (i j : Fin 4) :
    rightChange.val i j = rawCoordinates Ambient (rightRawBasis j) i :=
  rawBasis_repr true _ _

theorem rightChange_inv_entry (i j : Fin 4) :
    (rightChange⁻¹).val i j = rightRawBasis.repr (rawBasis true j) i := rfl

/-- Genuine linear-map matrices in the two actual bases are related by
the actual two derived units, for every original raw linear map. -/
theorem hom_matrix_change (h : RawHom) :
    LinearMap.toMatrix leftRawBasis rightRawBasis h =
      (rightChange⁻¹).val * LinearMap.toMatrix (rawBasis false) (rawBasis true) h * leftChange.val := by
  change LinearMap.toMatrix leftRawBasis rightRawBasis h =
    rightRawBasis.toMatrix (rawBasis true) *
      LinearMap.toMatrix (rawBasis false) (rawBasis true) h *
        (rawBasis false).toMatrix leftRawBasis
  rw [← LinearMap.toMatrix_id_eq_basis_toMatrix,
    ← LinearMap.toMatrix_id_eq_basis_toMatrix]
  rw [← LinearMap.toMatrix_comp (rawBasis false) (rawBasis true) rightRawBasis,
    ← LinearMap.toMatrix_comp leftRawBasis (rawBasis false) rightRawBasis]
  simp only [LinearMap.id_comp, LinearMap.comp_id]

theorem coordinateBasis_toMatrix (ij : Index) (h : RawHom) :
    coordinateBasis ij h = LinearMap.toMatrix (rawBasis false) (rawBasis true) h ij.1 ij.2 :=
  M9.SemilinearHomCoordinates.coordinateBasis_apply Ambient (ActualRaw false) (ActualRaw true)
    (rawBasis false) (rawBasis true) ij h

/-- The actual invariant linear functionals, expanded in the actual raw
sixteen coordinate functionals, with their original ambient coefficients. -/
theorem rawCoordinateBasis_expansion (i j : Fin 4) :
    rawCoordinateBasis (i,j) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        ((rightChange⁻¹).val i a * leftChange.val b j) • coordinateBasis (a,b) := by
  apply LinearMap.ext
  intro h
  rw [rawCoordinateBasis_apply, hom_matrix_change]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    coordinateBasis_toMatrix, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def linearCoordinate : RawDual →ₗ[Ambient] RawField :=
  (IsScalarTower.toAlgHom Ambient RawRing RawField).toLinearMap.comp
    (SymmetricAlgebra.ι Ambient RawDual)

def descendedMatrix : Matrix (Fin 4) (Fin 4) RawField := fun i j =>
  (fixedCoordinate (i,j) : RawField)

theorem descendedMatrix_entry (i j : Fin 4) :
    descendedMatrix i j =
      ∑ a : Fin 4, ∑ b : Fin 4,
        algebraMap Ambient RawField ((rightChange⁻¹).val i a * leftChange.val b j) * rawMatrix a b := by
  change linearCoordinate (rawCoordinateBasis (i,j)) = _
  rw [rawCoordinateBasis_expansion]
  simp only [map_sum, map_smul, Algebra.smul_def]
  rfl

/-- The universal original invariant-coordinate matrix is literally
R^-1 times the original raw matrix times L, with actual coefficient maps. -/
theorem descendedMatrix_eq_maps : descendedMatrix =
    ((rightChange⁻¹).val.map (algebraMap Ambient RawField)) * rawMatrix *
      (leftChange.val.map (algebraMap Ambient RawField)) := by
  ext i j
  rw [descendedMatrix_entry]
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def leftField : Matrix.GeneralLinearGroup (Fin 4) RawField :=
  Matrix.GeneralLinearGroup.map (algebraMap Ambient RawField) leftChange

def rightField : Matrix.GeneralLinearGroup (Fin 4) RawField :=
  Matrix.GeneralLinearGroup.map (algebraMap Ambient RawField) rightChange

theorem descendedMatrix_eq : descendedMatrix = (rightField⁻¹).val * rawMatrix * leftField.val :=
  descendedMatrix_eq_maps

theorem rightRawBasis_paired (j : Fin 4) :
    rightRawBasis j = actualRawTranspose (leftRawBasis j) := by
  rw [show rightRawBasis j = (actualRightBasis j).val from scalarExtendedBasis_apply _ _ _,
    actualRightBasis_paired, actualTransposeExchange_val,
    show leftRawBasis j = (actualLeftBasis j).val from scalarExtendedBasis_apply _ _ _]

/-- The right change of basis is the actual coefficient transpose of the
left one, proved from the original paired descended tensor bases. -/
theorem rightChange_eq_transpose_left :
    rightChange = Matrix.GeneralLinearGroup.map nativeTranspose.toRingHom leftChange := by
  apply Units.ext
  ext i j
  change rightChange.val i j = nativeTranspose (leftChange.val i j)
  rw [rightChange_entry, leftChange_entry, rightRawBasis_paired]
  exact FrameHomRawOddCoordinates.rawTranspose_coordinates _ _

theorem descendedMatrix_eq_transpose_gauge : descendedMatrix =
    ((Matrix.GeneralLinearGroup.map nativeTranspose.toRingHom leftChange)⁻¹).val.map
        (algebraMap Ambient RawField) * rawMatrix * leftChange.val.map (algebraMap Ambient RawField) := by
  rw [descendedMatrix_eq_maps, rightChange_eq_transpose_left]

end M9Native.FrameHomRawDescendedMatrices

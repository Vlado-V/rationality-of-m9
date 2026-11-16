module

public import M9StacksIntegration.FrameHomRawMatrixCoordinates
public import M9StacksIntegration.FrameRawSemilinearCoordinates

/-! The actual contragredient action on raw Hom coordinates.
The tensor-evaluation bases and all sixteen variables are the original
ones. The ambient coefficient action is retained throughout. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open Module
namespace M9Native.FrameHomRawMatrixAction
open M9.FrameBundleDescent (Ambient Even sideFactor)
open M9.FrameBundleDescent.Standard (ActualRaw)
open M9.FrameHomFieldDescent (RawHom RawDual RawRing RawField)
open M9.DeterminantFrameScalarExtension (rawCoordinates)
open ConicRawGammaMatrices FrameHomRawMatrixCoordinates FrameRawSemilinearCoordinates

local instance ambientEvenAction : MulSemiringAction Even Ambient :=
  M9.FrameQuadraticExtension.evenAction
local instance ambientEvenCommutes : SMulCommClass Even ℂ Ambient where
  smul_comm g c x :=
    map_smul (M9.FrameQuadraticExtension.evenRepresentation g).toLinearEquiv c x

theorem coordinateBasis_apply_rawBasis (ij : Index) (h : RawHom) :
    coordinateBasis ij h = rawCoordinates Ambient (h (rawBasis false ij.2)) ij.1 := by
  exact (coordinateBasis_apply ij h).trans
    (congrArg (fun x : ActualRaw false => rawCoordinates Ambient (h x) ij.1)
      (rawBasis_apply false ij.2).symm)

theorem rawBasis_smul (side : Bool) (g : Even) (j : Fin 4) :
    g • rawBasis side j =
      ∑ a : Fin 4, (gammaK Ambient (sideFactor side g)).val a j • rawBasis side a := by
  calc
    _ = ∑ a : Fin 4, (rawBasis side).repr (g • rawBasis side j) a • rawBasis side a :=
      ((rawBasis side).sum_repr _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      rw [rawBasis_repr, rawCoordinates_smul]
      have hc : (fun b => g • rawCoordinates Ambient (rawBasis side j) b) = Pi.single j 1 := by
        funext b
        rw [rawBasis_apply, LinearEquiv.apply_symm_apply]
        by_cases hb : b = j <;> simp [hb]
      rw [hc, Matrix.mulVec_single_one]
      rfl

theorem coordinateBasis_action_apply (g : Even) (ij : Index) (h : RawHom) :
    (g • coordinateBasis ij) h =
      ∑ a : Fin 4, ∑ b : Fin 4,
        (gammaK Ambient g.2⁻¹).val ij.1 a * (gammaK Ambient g.1).val b ij.2 *
          coordinateBasis (a,b) h := by
  rw [M9.FrameHomFieldDescent.rawDualAction_apply, coordinateBasis_apply_rawBasis,
    M9.FrameHomFieldDescent.rawHomAction_apply]
  simp only [inv_inv]
  rw [rawCoordinates_inv_smul_cancel]
  change (∑ a : Fin 4, (gammaK Ambient g.2⁻¹).val ij.1 a *
    rawCoordinates Ambient (h (g • rawBasis false ij.2)) a) = _
  refine (congrArg (fun x : ActualRaw false =>
    ∑ a : Fin 4, (gammaK Ambient g.2⁻¹).val ij.1 a * rawCoordinates Ambient (h x) a)
      (rawBasis_smul false g ij.2)).trans ?_
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, coordinateBasis_apply_rawBasis, mul_assoc]
  rfl

theorem coordinateBasis_action (g : Even) (ij : Index) :
    g • coordinateBasis ij =
      ∑ a : Fin 4, ∑ b : Fin 4,
        ((gammaK Ambient g.2⁻¹).val ij.1 a * (gammaK Ambient g.1).val b ij.2) •
          coordinateBasis (a,b) := by
  apply LinearMap.ext
  intro h
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using
    coordinateBasis_action_apply g ij h

theorem rawFieldAction_entry (g : Even) (i j : Fin 4) :
    letI := M9.FrameHomFieldDescent.rawFieldAction
    g • rawMatrix i j =
      ∑ a : Fin 4, ∑ b : Fin 4,
        algebraMap Ambient RawField
          ((gammaK Ambient g.2⁻¹).val i a * (gammaK Ambient g.1).val b j) * rawMatrix a b := by
  let := M9.FrameHomFieldDescent.rawFieldAction
  let ι : RawDual →ₗ[Ambient] RawField :=
    (IsScalarTower.toAlgHom Ambient RawRing RawField).toLinearMap.comp
      (SymmetricAlgebra.ι Ambient RawDual)
  calc
    g • rawMatrix i j = ι (g • coordinateBasis (i,j)) :=
      M9.FrameHomFieldDescent.rawFieldAction_degreeOne g (coordinateBasis (i,j))
    _ = _ := by
      rw [coordinateBasis_action]
      simp only [map_sum, map_smul, Algebra.smul_def]
      rfl

theorem rawFieldAction_matrix (g : Even) :
    letI := M9.FrameHomFieldDescent.rawFieldAction
    (fun i j => g • rawMatrix i j) =
      ((((gammaK Ambient g.2)⁻¹).val).map (algebraMap Ambient RawField)) * rawMatrix *
        ((gammaK Ambient g.1).val.map (algebraMap Ambient RawField)) := by
  let := M9.FrameHomFieldDescent.rawFieldAction
  ext i j
  rw [rawFieldAction_entry]
  simp only [← map_inv, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem rawFieldAction_coefficient (g : Even) (a : Ambient) :
    letI := M9.FrameHomFieldDescent.rawFieldAction
    g • algebraMap Ambient RawField a = algebraMap Ambient RawField (g • a) :=
  M9.FrameHomFieldDescent.rawFieldAction_coefficient g a

end M9Native.FrameHomRawMatrixAction
end

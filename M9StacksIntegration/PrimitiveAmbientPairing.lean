module

public import M9StacksIntegration.PrimitiveRingMatrices
public import M9StacksIntegration.LagrangianSigmaInvariance
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! The actual exterior wedge pairing is symplectically invariant over every coefficient ring. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module Matrix exteriorPower

universe u

namespace M9Native.PrimitiveAmbientPairing

open LagrangianRing LagrangianTransitivity PrimitiveRingRepresentation PrimitiveRingMatrices

variable (R : Type u) [CommRing R]

def volumeCoordinate : (⋀[R]^6 (V R)) →ₗ[R] R :=
  exteriorPower.pairingDual R (V R) 6
    (exteriorPower.ιMulti R 6 (fun i : Fin 6 => LinearMap.proj i))

def ambientPairing : LinearMap.BilinForm R (Third R) :=
  (exteriorPower.wedge R (V R) 3 3).compr₂ (volumeCoordinate R)

theorem wedge_ιMulti (v w : Fin 3 → V R) :
    exteriorPower.wedge R (V R) 3 3 (exteriorPower.ιMulti R 3 v)
      (exteriorPower.ιMulti R 3 w) = exteriorPower.ιMulti R 6 (Fin.append v w) := by
  apply Subtype.ext
  simp only [exteriorPower.wedge, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]

theorem ambientPairing_ιMulti (v w : Fin 3 → V R) :
    ambientPairing R (exteriorPower.ιMulti R 3 v) (exteriorPower.ιMulti R 3 w) =
      Matrix.det (Matrix.of fun i j : Fin 6 => Fin.append v w i j) := by
  change volumeCoordinate R (exteriorPower.wedge R (V R) 3 3
    (exteriorPower.ιMulti R 3 v) (exteriorPower.ιMulti R 3 w)) = _
  rw [wedge_ιMulti]
  simp [volumeCoordinate]

theorem mappedRows (M : Matrix (Fin 6) (Fin 6) R) (U : Fin 6 → V R) :
    (Matrix.of fun i j : Fin 6 => M.mulVecLin (U i) j) =
      (Matrix.of fun i j : Fin 6 => U i j) * M.transpose := by
  ext i j
  change (∑ k : Fin 6, M j k * U i k) = ∑ k : Fin 6, U i k * M j k
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- This is an identity of the actual wedge pairing, using determinant one over the ring. -/
theorem ambientPairing_natural (g : Matrix.symplecticGroup (Fin 3) R) :
    (ambientPairing R).comp (exteriorAction R g) (exteriorAction R g) = ambientPairing R := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change ambientPairing R (exteriorAction R g (exteriorPower.ιMulti R 3 v))
    (exteriorAction R g (exteriorPower.ιMulti R 3 w)) =
      ambientPairing R (exteriorPower.ιMulti R 3 v) (exteriorPower.ιMulti R 3 w)
  simp only [exteriorAction, exteriorPower.map_apply_ιMulti, ambientPairing_ιMulti]
  have ha : Fin.append ((matrixSix R g).mulVecLin ∘ v) ((matrixSix R g).mulVecLin ∘ w) =
      (fun i => (matrixSix R g).mulVecLin (Fin.append v w i)) := by
    funext i
    exact Fin.addCases (m := 3) (n := 3)
      (fun _ => by simp only [Fin.append_left, Function.comp_apply])
      (fun _ => by simp only [Fin.append_right, Function.comp_apply]) i
  rw [ha, mappedRows, Matrix.det_mul, Matrix.det_transpose,
    LagrangianSigmaInvariance.matrixSix_det_eq_one, mul_one]

def gram : Matrix (Fin 20) (Fin 20) R :=
  LinearMap.BilinForm.toMatrix (thirdBasis20 R) (ambientPairing R)

theorem gram_apply (i j : Fin 20) :
    gram R i j = Matrix.det (Matrix.of fun a b : Fin 6 =>
      Fin.append (fun k => basisVector R (triple i k))
        (fun k => basisVector R (triple j k)) a b) := by
  rw [gram, LinearMap.BilinForm.toMatrix_apply, thirdBasis20_apply, thirdBasis20_apply,
    ambientPairing_ιMulti]

theorem gram_map {S : Type u} [CommRing S] (ρ : R →+* S) :
    gram S = (gram R).map ρ := by
  ext i j
  rw [gram_apply, Matrix.map_apply, gram_apply, RingHom.map_det]
  congr 1
  ext a b
  refine Fin.addCases (m := 3) (n := 3) (fun k => ?_) (fun k => ?_) a
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.append_left,
      basisVector, Pi.single_apply]
    split_ifs <;> simp only [map_one, map_zero]
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Fin.append_right,
      basisVector, Pi.single_apply]
    split_ifs <;> simp only [map_one, map_zero]

theorem exteriorMatrix_preserves_gram (g : Matrix.symplecticGroup (Fin 3) R) :
    (exteriorMatrix R g).transpose * gram R * exteriorMatrix R g = gram R := by
  have h := congrArg (LinearMap.BilinForm.toMatrix (thirdBasis20 R)) (ambientPairing_natural R g)
  rw [LinearMap.BilinForm.toMatrix_comp (b := thirdBasis20 R) (c := thirdBasis20 R)] at h
  exact h

end M9Native.PrimitiveAmbientPairing

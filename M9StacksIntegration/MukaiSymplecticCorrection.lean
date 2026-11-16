module

public import M9StacksIntegration.MukaiLagrangianMap
public import M9StacksIntegration.LagrangianSigmaInvariance

/-!
# Actual symplectic correction of a bivector similitude

The fixed standard exterior bivector determines the literal Mathlib
symplectic matrix condition after the original six-coordinate reindexing.
Over an algebraically closed field, a nonzero similitude multiplier is
corrected by an actual scalar square root.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module Matrix

universe u

namespace M9Native.MukaiSymplecticCorrection

open MukaiLagrangianMap LagrangianTransitivity

variable (k : Type u) [Field k]

theorem bivectorMatrix_map (M : Matrix (Fin 6) (Fin 6) k)
    (w : MukaiWedgeKernel.Bivector k 6) :
    MukaiWedgeKernel.bivectorMatrix k 6 (exteriorPower.map 2 M.mulVecLin w) =
      M * MukaiWedgeKernel.bivectorMatrix k 6 w * Mᵀ := by
  have hm : exteriorPower.map 2 M.mulVecLin =
      ExteriorAlgebra.powMapₛₗ 2 (RingHom.id k)
        (MukaiWedgeKernel.matrixEvaluation (RingHom.id k) M) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorPower.map 2 M.mulVecLin (exteriorPower.ιMulti k 2 v) =
      ExteriorAlgebra.powMapₛₗ 2 (RingHom.id k)
        (MukaiWedgeKernel.matrixEvaluation (RingHom.id k) M) (exteriorPower.ιMulti k 2 v)
    rw [exteriorPower.map_apply_ιMulti, ExteriorAlgebra.powMapₛₗ_ιMulti]
    rfl
  rw [hm, MukaiWedgeKernel.bivectorMatrix_naturality]
  rfl

/-- The matrix condition is obtained from the actual exterior-square relation. -/
theorem gram_of_sigma_scale (M : Matrix (Fin 6) (Fin 6) k) (a : k)
    (h : exteriorPower.map 2 M.mulVecLin (standardSigma k) = a • standardSigma k) :
    M * standardMatrix k * Mᵀ = a • standardMatrix k := by
  have hh := congrArg (MukaiWedgeKernel.bivectorMatrix k 6) h
  rw [bivectorMatrix_map, map_smul, standardSigma_matrix] at hh
  exact hh

/-- A literal six-coordinate standard-form matrix is an actual native Sp6 matrix. -/
def nativeSymplectic (M : Matrix (Fin 6) (Fin 6) k)
    (hM : M * standardMatrix k * Mᵀ = standardMatrix k) :
    Matrix.symplecticGroup (Fin 3) k := by
  let re := Matrix.reindexAlgEquiv k k (splitIndex.symm : Fin 6 ≃ SplitIndex)
  have hJ : re (standardMatrix k) = -Matrix.J (Fin 3) k := by
    ext i j
    change -Matrix.J (Fin 3) k (splitIndex.symm (splitIndex i))
      (splitIndex.symm (splitIndex j)) = _
    simp
  have hT : re Mᵀ = (re M)ᵀ := rfl
  have hh := congrArg re hM
  rw [map_mul, map_mul, hJ, hT] at hh
  refine ⟨re M, SymplecticGroup.mem_iff.mpr ?_⟩
  apply neg_injective
  simpa only [Matrix.mul_neg, Matrix.neg_mul] using hh

theorem matrixSix_nativeSymplectic (M : Matrix (Fin 6) (Fin 6) k)
    (hM : M * standardMatrix k * Mᵀ = standardMatrix k) :
    matrixSix k (nativeSymplectic k M hM) = M := by
  ext i j
  change M (splitIndex (splitIndex.symm i)) (splitIndex (splitIndex.symm j)) = M i j
  simp

/-- The scalar correction and its actual native symplectic matrix are constructed,
not supplied as a normalization hypothesis. -/
theorem exists_scaled_symplectic [IsAlgClosed k]
    (M : Matrix (Fin 6) (Fin 6) k) (a : k) (ha : a ≠ 0)
    (hσ : exteriorPower.map 2 M.mulVecLin (standardSigma k) = a • standardSigma k) :
    ∃ (t : k) (g : Matrix.symplecticGroup (Fin 3) k),
      t ≠ 0 ∧ t ^ 2 * a = 1 ∧ matrixSix k g = t • M := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (n := 2) (by decide)
  have ht0 : t ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at ht
    exact (inv_ne_zero ha) ht.symm
  have hta : t ^ 2 * a = 1 := by rw [ht, inv_mul_cancel₀ ha]
  have hM := gram_of_sigma_scale k M a hσ
  have hG : (t • M) * standardMatrix k * (t • M)ᵀ = standardMatrix k := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hM, smul_smul]
    have ht' : t * t * a = 1 := by simpa only [pow_two] using hta
    rw [ht', one_smul]
  exact ⟨t, nativeSymplectic k (t • M) hG, ht0, hta,
    matrixSix_nativeSymplectic k (t • M) hG⟩

end M9Native.MukaiSymplecticCorrection

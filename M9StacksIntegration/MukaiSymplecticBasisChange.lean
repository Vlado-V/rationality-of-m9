module

public import M9StacksIntegration.MukaiKernelChoices
public import M9StacksIntegration.MukaiSymplecticCorrection

/-!
# Native symplectic basis changes from the actual Mukai bundle isomorphism

The multiplier is derived from the original exterior-evaluation kernel line.
The constructed native symplectic matrix is an actual scalar multiple of
the complete-section coordinate matrix of the original sheaf isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module Matrix
open scoped BigOperators

universe u

namespace M9Native.MukaiSymplecticBasisChange

open MukaiLagrangianMap MukaiEvaluationChoices

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

def coordinateEquiv {E F : X.Modules} (e : E ≅ F)
    (bE : Basis (Fin 6) k (H0 k f E)) (bF : Basis (Fin 6) k (H0 k f F)) :
    (Fin 6 → k) ≃ₗ[k] (Fin 6 → k) :=
  bE.equivFun.symm.trans ((h0Equiv k f e).trans bF.equivFun)

def coordinateMatrix {E F : X.Modules} (e : E ≅ F)
    (bE : Basis (Fin 6) k (H0 k f E)) (bF : Basis (Fin 6) k (H0 k f F)) :
    Matrix (Fin 6) (Fin 6) k := LinearMap.toMatrix' (coordinateEquiv k f e bE bF).toLinearMap

theorem coordinateMatrix_mulVec {E F : X.Modules} (e : E ≅ F)
    (bE : Basis (Fin 6) k (H0 k f E)) (bF : Basis (Fin 6) k (H0 k f F)) (v : Fin 6 → k) :
    coordinateMatrix k f e bE bF *ᵥ v = bF.equivFun (h0Equiv k f e (bE.equivFun.symm v)) :=
  LinearMap.toMatrix'_mulVec _ _

theorem coordinateMatrix_column {E F : X.Modules} (e : E ≅ F)
    (bE : Basis (Fin 6) k (H0 k f E)) (bF : Basis (Fin 6) k (H0 k f F)) (j : Fin 6) :
    (coordinateMatrix k f e bE bF).col j = bF.equivFun (h0Equiv k f e (bE j)) := by
  rw [← Matrix.mulVec_single_one, coordinateMatrix_mulVec, Basis.equivFun_symm_single]

theorem basisSigma_as_map {E : X.Modules} (b : Basis (Fin 6) k (H0 k f E)) :
    exteriorPower.map 2 b.equivFun.symm.toLinearMap (standardSigma k) = basisSigma k f E b := by
  simp only [standardSigma, basisSigma, map_sum, exteriorPower.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> simp

/-- Complete-basis coordinates intertwine the original exterior-square map. -/
theorem coordinateMatrix_sigma {E F : X.Modules} (e : E ≅ F)
    (bE : Basis (Fin 6) k (H0 k f E)) (bF : Basis (Fin 6) k (H0 k f F)) :
    exteriorPower.map 2 (coordinateMatrix k f e bE bF).mulVecLin (standardSigma k) =
      MukaiWedgeKernel.coordinateBivector k f F bF
        (exteriorPower.map 2 (h0Equiv k f e).toLinearMap (basisSigma k f E bE)) := by
  have hM : (coordinateMatrix k f e bE bF).mulVecLin =
      (coordinateEquiv k f e bE bF).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact coordinateMatrix_mulVec k f e bE bF v
  rw [hM]
  change exteriorPower.map 2 (bF.equivFun.toLinearMap.comp
    ((h0Equiv k f e).toLinearMap.comp bE.equivFun.symm.toLinearMap)) (standardSigma k) =
      exteriorPower.map 2 bF.equivFun.toLinearMap
        (exteriorPower.map 2 (h0Equiv k f e).toLinearMap (basisSigma k f E bE))
  rw [exteriorPower.map_comp, exteriorPower.map_comp]
  change exteriorPower.map 2 bF.equivFun.toLinearMap
    (exteriorPower.map 2 (h0Equiv k f e).toLinearMap
      (exteriorPower.map 2 bE.equivFun.symm.toLinearMap (standardSigma k))) = _
  rw [basisSigma_as_map]

variable [CharZero k] [IsAlgClosed k] [IsProper f] [IsCurve k f]

/-- The native Sp6 matrix and scalar are derived from the actual original
bundle isomorphism and normalized complete section bases. -/
theorem exists_symplectic_coordinate_change {E F : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3]
    (e : E ≅ F) (bE : Basis (Fin 6) k (H0 k f E)) (bF : Basis (Fin 6) k (H0 k f F))
    (cF : Scheme.Modules.exteriorPower F (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f F 3)
    (hE : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E bE) = 0)
    (hF : ExteriorEvaluation.lambda k f F 2 (basisSigma k f F bF) = 0) :
    ∃ (t : k) (g : Matrix.symplecticGroup (Fin 3) k), t ≠ 0 ∧
      LagrangianTransitivity.matrixSix k g = t • coordinateMatrix k f e bE bF := by
  obtain ⟨a, ha, hscale⟩ := MukaiKernelChoices.exists_basisSigma_scale k f e bE bF cF hg hsemi hE hF
  have hσ : exteriorPower.map 2 (coordinateMatrix k f e bE bF).mulVecLin (standardSigma k) =
      a • standardSigma k := by
    rw [coordinateMatrix_sigma, hscale, map_smul, coordinateBivector_basisSigma]
  obtain ⟨t, g, ht, _, hg⟩ :=
    MukaiSymplecticCorrection.exists_scaled_symplectic k (coordinateMatrix k f e bE bF) a ha hσ
  exact ⟨t, g, ht, hg⟩

end M9Native.MukaiSymplecticBasisChange

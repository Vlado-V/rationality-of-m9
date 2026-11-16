module

public import M9StacksIntegration.PrimitiveRingMatrices
public import M9StacksIntegration.LagrangianSigmaInvariance

/-! The literal positive primitive Plücker action on quotient rows.
It is the third exterior action of the transpose, over the original
coefficient ring, without replacing coefficient duality by an alternating form. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open Module Matrix

universe u

namespace M9Native.LagrangianPrimitiveRowAction

open LagrangianRing LagrangianTransitivity LagrangianSigmaInvariance PrimitiveRingMatrices

variable (R : Type u) [CommRing R]

/-- Actual quotient rows transform by the transpose on actual third exterior vectors. -/
theorem rowPlucker_mul_right (M : Matrix (Fin 3) (Fin 6) R)
    (G : Matrix (Fin 6) (Fin 6) R) :
    rowPlucker R (M*G) = exteriorPower.map 3 G.transpose.mulVecLin (rowPlucker R M) := by
  rw [rowPlucker,rowPlucker,exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti R 3)
  funext i j
  change ∑ k : Fin 6,M i k*G k j = ∑ k : Fin 6,G k j*M i k
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem rowTwenty_mul_symplectic (M : Matrix (Fin 3) (Fin 6) R)
    (g : Matrix.symplecticGroup (Fin 3) R) :
    rowTwenty R (M*matrixSix R g) =
      exteriorMatrix R (transposeSymplectic R g) *ᵥ rowTwenty R M := by
  rw [rowTwenty,rowPlucker_mul_right]
  change (thirdBasis20 R).equivFun
      (PrimitiveRingRepresentation.exteriorAction R (transposeSymplectic R g) (rowPlucker R M)) = _
  exact (exteriorMatrix_coordinates R (transposeSymplectic R g) (rowPlucker R M)).symm

variable (K : Type u) [Field K] [CharZero K] (κ : K →+* R)

/-- The fourteen original primitive coordinates have the genuine
positive transpose action. Isotropy is used only for the proved primitive reconstruction. -/
theorem rowFourteen_mul_symplectic (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j,LagrangianRing.omega R (M i) (M j)=0)
    (g : Matrix.symplecticGroup (Fin 3) R) :
    rowFourteen R κ (M*matrixSix R g) =
      matrix14 R K κ (transposeSymplectic R g) *ᵥ rowFourteen R κ M := by
  rw [rowFourteen,rowTwenty_mul_symplectic,matrix14,rowFourteen]
  have h := congrArg (fun v : Fin 20 → R =>
    (LagrangianField.projectionMatrix K).map (fun c => κ c) *ᵥ
      (exteriorMatrix R (transposeSymplectic R g) *ᵥ v))
        (primitive_reconstruction R κ M hM)
  simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using h.symm

end M9Native.LagrangianPrimitiveRowAction

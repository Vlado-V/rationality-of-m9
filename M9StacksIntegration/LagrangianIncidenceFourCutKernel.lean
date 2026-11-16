module

public import M9StacksIntegration.LagrangianIncidenceFourCutBase
public import M9StacksIntegration.LineSectionZeroRowDrop

/-! The actual GL5 change and the original model kernel identify the
full pulled five-equation ideal with the full remaining four-section
ideal once the actual first pulled section vanishes. The separate
incidence quotient theorem proves that geometric first-row vanishing
for the selected original triple; it is not assumed by the final
original-curve comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.LagrangianIncidenceFourCutKernel
open LagrangianOrderedFibre LagrangianPluckerQuotient LagrangianHyperplaneCoordinates
open LagrangianIncidenceFourCutBase
variable (K : Type u) [Field K] [CharZero K]

theorem model_kernel_comap_eq_fourIdeal_of_first_zero
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
    (w : Fin 2 → (Fin 6 → K)) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hzero : pullbackGlobalSections (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
      (determinantLine K) (determinantSection K ((A.val * M) 0)) = 0) :
    (modelInclusion K M hM).ker.comap
      (LagrangianArbitraryPlaneIncidence.incidenceToLG K w) =
        fourIdeal K w (A.val * M) := by
  rw [LagrangianMatrixRowChange.modelInclusion_ker,
    LagrangianMatrixRowChange.equationIdeal_eq K A M,
    LagrangianBetaFourCut.fiveIdeal_eq_first_sup_remaining,
    Scheme.IdealSheafData.comap_sup, ← Stacks.Divisors.zeroScheme_pullback,
    hzero, LineSectionZeroRowDrop.zeroSection_ideal_eq_bot, bot_sup_eq]
  exact (fourIdeal_eq_comap_remaining K w (A.val * M)).symm

end M9Native.LagrangianIncidenceFourCutKernel

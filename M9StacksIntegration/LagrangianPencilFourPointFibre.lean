module

public import M9StacksIntegration.PencilFourPointFibre
public import M9StacksIntegration.LagrangianNoTrigonal

/-!
# Four actual pencil-fibre points on the original transverse LG curve

The no-degree-three premise is discharged by the original LG quadratic
ideal theorem. The remaining input is the original degree-four pencil.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianPencilFourPointFibre

open LagrangianTransverseRestriction PencilFourPointFibre

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- All four points, the original map of degree four, its finite-flat
rank, and its full étale fibre are constructed from the original curve
and pencil, with no genus or lower-pencil premise. -/
theorem nonempty_fourPointFibre (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (curve K M) ≤ 1)
    (A : LinearSeries K (curveProjection K M) hdim 4 1) :
    Nonempty (FourPointFibre K (curveProjection K M)) := by
  let : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  exact PencilFourPointFibre.nonempty_fourPointFibre hdim A
    (LagrangianNoTrigonal.no_g1_three_at_dimension K M hM hdim)

end M9Native.LagrangianPencilFourPointFibre

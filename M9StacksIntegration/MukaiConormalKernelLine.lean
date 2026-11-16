module

public import M9StacksIntegration.MukaiConormalFieldAvoidance
public import M9StacksIntegration.MukaiGenericRankBound
public import M9StacksIntegration.ClosedPointCurveRank

@[expose] public section

/-! The actual categorical conormal-evaluation kernel in the bad generic
rank branch is a genuine line bundle. Legacy visibility is necessary
only because the frozen native closed-point semicontinuity providers use
legacy visibility. Their source and proof bodies are preserved.

The rank-one conclusion is derived from actual Semi3 and the actual
generic rank bound; no constant-rank or kernel-rank premise is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalKernelLine

open MukaiCubicCurveKernel MukaiPrimitiveCanonicalEvaluation

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

theorem closed_rank_six
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hgen : MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X) ≤ 6)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) x = 6 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  let := determinantH0_finite K f E
  have hlo := MukaiConormalFieldAvoidance.six_le_mapRankAt K f E b d hσ hsemi
    (pointOfClosedPoint f x hx) (pointOfClosedPoint_comp f x hx)
  simp only [pointOfClosedPoint_apply] at hlo
  have hhi := MukaiGenericRankBound.mapRankAt_le_generic
    (curveEvaluationMap K f E b d) 7 (finrank K (DeterminantH0 K f E))
    (curveSource_rank K f E b d)
    (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E))) x
  omega

theorem everywhere_rank_six
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hgen : MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X) ≤ 6) :
    MukaiSemiIrreducible.EverywhereRank (curveEvaluationMap K f E b d) 6 := by
  let := determinantH0_finite K f E
  exact ClosedPointCurveRank.everywhereRank_of_closedRank K f
    (curveEvaluationMap K f E b d) 7 (finrank K (DeterminantH0 K f E)) 6
    (curveSource_rank K f E b d)
    (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E)))
    (closed_rank_six K f E b d hσ hsemi hgen)

/-- The line is the original categorical kernel of the original
conormal-to-original-determinant-evaluation sheaf map. -/
theorem kernel_rank_one
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hgen : MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X) ≤ 6) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (curveKernel K f E b d) 1 := by
  let := determinantH0_finite K f E
  exact (ClosedPointCurveRank.ranks_of_closedRank K f
    (curveEvaluationMap K f E b d) 7 (finrank K (DeterminantH0 K f E)) 6
    (curveSource_rank K f E b d)
    (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E)))
    (closed_rank_six K f E b d hσ hsemi hgen)).1

end M9Native.MukaiConormalKernelLine

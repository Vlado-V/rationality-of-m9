module

public import M9StacksIntegration.LagrangianTransverseTripleRank
public import M9StacksIntegration.LagrangianGoodOpenRestriction
public import M9StacksIntegration.MukaiTripleDeterminantRank

/-! Actual determinant-zero independent original triples have rank two
everywhere. This directly consumes a genuine determinant-zero triple
producer, without a separate nonmonicity or chosen rank-two premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.LagrangianOriginalDeterminantRankTwo

open LagrangianOrderedFibre LagrangianUniversalSections LagrangianUniversalTriples
open LagrangianTripleDeterminantSection

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
  (M : Matrix (Fin 5) (Fin 14) k) (hM : Function.Surjective M.mulVec)

/-- Genuine original determinant vanishing, not supplied nonmonicity, gives actual everywhere rank two. -/
theorem everywhereRank_of_determinantValue_eq_zero
    [IsIntegral (model k M hM)] [SmoothOfRelativeDimension 1 (modelProjection k M hM)]
    (s : Fin 3 → (Fin 6 → k)) (hs : LinearIndependent k s)
    (hdet : determinantValue k (modelProjection k M hM) (modelInclusion k M hM) s = 0) :
    MukaiSemiIrreducible.EverywhereRank
      (evaluation k (modelProjection k M hM) (modelInclusion k M hM) s) 2 := by
  have hv := (determinantValue_eq_zero_iff k (modelProjection k M hM)
    (modelInclusion k M hM) rfl s).mp hdet
  obtain ⟨a,ha,h⟩ := LagrangianModelRestriction.exists_nonzero_vecMul_of_restriction_eq_zero
    k M hM (PrimitiveDecomposableNonzero.coefficients k s) hv
      (PrimitiveDecomposableNonzero.coefficients_ne_zero k s hs)
  letI := bundle_rank k (modelInclusion k M hM)
  intro x
  exact Nat.le_antisymm
    (MukaiTripleDeterminantRank.mapRankAt_le_two_of_lambda_eq_zero k (modelProjection k M hM)
      (bundle k (modelInclusion k M hM))
      (fun i => sectionMap k (modelProjection k M hM) (modelInclusion k M hM) (s i)) hdet x)
    (LagrangianTransverseTripleRank.two_le_mapRankAt_of_relation k M hM a ha s h x)

/-- The actual canonical good open derives all geometry for the determinant-zero producer application. -/
theorem everywhereRank_of_determinantValue_eq_zero_of_goodOpen
    (hg : LagrangianMatrixPointRows.matrixPoint k M hM (IsLocalRing.closedPoint k) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen k)
    (s : Fin 3 → (Fin 6 → k)) (hs : LinearIndependent k s)
    (hdet : determinantValue k (modelProjection k M hM) (modelInclusion k M hM) s = 0) :
    MukaiSemiIrreducible.EverywhereRank
      (evaluation k (modelProjection k M hM) (modelInclusion k M hM) s) 2 := by
  letI := LagrangianGoodOpenRestriction.model_integral k M hM hg
  letI := LagrangianGoodOpenRestriction.model_smooth k M hM hg
  exact everywhereRank_of_determinantValue_eq_zero k M hM s hs hdet

end M9Native.LagrangianOriginalDeterminantRankTwo

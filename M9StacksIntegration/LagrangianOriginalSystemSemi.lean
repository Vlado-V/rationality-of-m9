module

public import M9StacksIntegration.LagrangianTransverseTripleRank
public import M9StacksIntegration.LagrangianOriginalTripleAlternative
public import M9StacksIntegration.LagrangianGoodOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Genuine Semi3 for the original six-section system on a transverse LG section

Every independent triple in the original constant six-space either
induces a sheaf monomorphism, or has rank exactly two at every actual
residue point. The primitive five-row kernel is the true computed
kernel of the original cut; the nonzero local differential follows
from the actual native conormal sequence and the literal determinant.
The good-open wrapper derives both curve geometry hypotheses from the
original parameter, with no Semi or complete-H0 premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.LagrangianOriginalSystemSemi

open LagrangianFiveSectionModel LagrangianUniversalSections LagrangianUniversalTriples
open LagrangianOrderedFibre

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
  (M : Matrix (Fin 5) (Fin 14) k) (hM : Function.Surjective M.mulVec)

/-- The actual original six-section system is Semi3 on the true smooth integral five-section. -/
theorem original_triple_alternative
    [IsIntegral (model k M hM)] [SmoothOfRelativeDimension 1 (modelProjection k M hM)]
    (s : Fin 3 → (Fin 6 → k)) (hs : LinearIndependent k s) :
    Mono (evaluation k (modelProjection k M hM) (modelInclusion k M hM) s) ∨
      MukaiSemiIrreducible.EverywhereRank
        (evaluation k (modelProjection k M hM) (modelInclusion k M hM) s) 2 := by
  letI : Smooth (modelProjection k M hM) := SmoothOfRelativeDimension.smooth 1 _
  have hreg := isRegular_of_smooth_over_field (modelProjection k M hM)
  have hdim := (topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (modelProjection k M hM) 1).le
  obtain hm | ⟨hv0,hv,hupper⟩ := LagrangianOriginalTripleAlternative.original_triple_alternative
    k (modelProjection k M hM) (modelInclusion k M hM) hreg hdim rfl s hs
  · exact Or.inl hm
  · obtain ⟨a,ha,h⟩ := LagrangianModelRestriction.exists_nonzero_vecMul_of_restriction_eq_zero
      k M hM (PrimitiveDecomposableNonzero.coefficients k s) hv hv0
    exact Or.inr (fun x => Nat.le_antisymm (hupper x)
      (LagrangianTransverseTripleRank.two_le_mapRankAt_of_relation k M hM a ha s h x))

/-- On the original canonical good open all required curve geometry is derived from the parameter. -/
theorem original_triple_alternative_of_goodOpen
    (hg : LagrangianMatrixPointRows.matrixPoint k M hM (IsLocalRing.closedPoint k) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen k)
    (s : Fin 3 → (Fin 6 → k)) (hs : LinearIndependent k s) :
    Mono (evaluation k (modelProjection k M hM) (modelInclusion k M hM) s) ∨
      MukaiSemiIrreducible.EverywhereRank
        (evaluation k (modelProjection k M hM) (modelInclusion k M hM) s) 2 := by
  letI := LagrangianGoodOpenRestriction.model_integral k M hM hg
  letI := LagrangianGoodOpenRestriction.model_smooth k M hM hg
  exact original_triple_alternative k M hM s hs

end M9Native.LagrangianOriginalSystemSemi

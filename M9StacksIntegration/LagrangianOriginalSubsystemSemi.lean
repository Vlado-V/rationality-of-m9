module

public import M9StacksIntegration.LagrangianOriginalSystemSemi

/-!
# Native Semi3 of the genuine image of the original six-section map

Every independent triple in the actual image has original preimages;
independence of the images implies independence of those preimages.
The original triple theorem therefore gives the literal native Semi
predicate on the actual section subspace. No injectivity, dimension,
H0 completeness, or Semi premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.LagrangianOriginalSubsystemSemi

open LagrangianOrderedFibre LagrangianUniversalSections

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
  (M : Matrix (Fin 5) (Fin 14) k) (hM : Function.Surjective M.mulVec)

/-- The literal image of the original actual six-section map. -/
abbrev originalSubsystem :
    Submodule k (cohomologyOverField k (modelProjection k M hM)
      (bundle k (modelInclusion k M hM)) 0) :=
  LinearMap.range (sectionMap k (modelProjection k M hM) (modelInclusion k M hM))

/-- Actual native Semi3 of the original induced section subspace. -/
theorem originalSubsystem_semi
    [IsIntegral (model k M hM)] [SmoothOfRelativeDimension 1 (modelProjection k M hM)] :
    MukaiSemiIrreducible.SemiIrreducible k (modelProjection k M hM)
      (bundle k (modelInclusion k M hM)) 3 (originalSubsystem k M hM) := by
  classical
  intro t ht
  choose v hv using (fun i : Fin 3 => (t i).property)
  have hti : LinearIndependent k
      (fun i => (t i : cohomologyOverField k (modelProjection k M hM)
        (bundle k (modelInclusion k M hM)) 0)) :=
    ht.map' (originalSubsystem k M hM).subtype (by simp)
  have hseq : (fun i => sectionMap k (modelProjection k M hM)
      (modelInclusion k M hM) (v i)) =
      (fun i => (t i : cohomologyOverField k (modelProjection k M hM)
        (bundle k (modelInclusion k M hM)) 0)) := funext hv
  have hjv : LinearIndependent k (fun i => sectionMap k (modelProjection k M hM)
      (modelInclusion k M hM) (v i)) :=
    (congrArg (fun z : Fin 3 → cohomologyOverField k (modelProjection k M hM)
      (bundle k (modelInclusion k M hM)) 0 => LinearIndependent k z) hseq).mpr hti
  have hvli : LinearIndependent k v :=
    LinearIndependent.of_comp (sectionMap k (modelProjection k M hM) (modelInclusion k M hM)) hjv
  have h := LagrangianOriginalSystemSemi.original_triple_alternative k M hM v hvli
  simpa only [LagrangianUniversalTriples.evaluation,hseq] using h

/-- On the actual canonical good open all curve geometry in the native Semi statement is derived. -/
theorem originalSubsystem_semi_of_goodOpen
    (hg : LagrangianMatrixPointRows.matrixPoint k M hM (IsLocalRing.closedPoint k) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen k) :
    MukaiSemiIrreducible.SemiIrreducible k (modelProjection k M hM)
      (bundle k (modelInclusion k M hM)) 3 (originalSubsystem k M hM) := by
  letI := LagrangianGoodOpenRestriction.model_integral k M hM hg
  letI := LagrangianGoodOpenRestriction.model_smooth k M hM hg
  exact originalSubsystem_semi k M hM

end M9Native.LagrangianOriginalSubsystemSemi

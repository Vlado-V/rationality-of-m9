module

public import M9StacksIntegration.MukaiLagrangianClosedImmersion
public import M9StacksIntegration.MukaiExteriorEvaluationSurjectivity

@[expose] public section

/-!
# The genuine Mukai curve map is a closed immersion

The actual curve-kernel argument supplies third exterior surjectivity
for the given complete rank-three system. The canonical separation
criterion therefore applies to the original normalized map. In the final
existence theorem the normalization and original incidence fibre are
constructed internally from the actual bundle; no surjectivity or
embedding is assumed.

Identifying that entire incidence fibre with the original curve is a
further geometric assertion and is not claimed here.

This consumer retains the frozen exterior producer's legacy visibility;
its frozen upstream source and objects are not altered.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.MukaiActualLagrangianClosedImmersion

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation MukaiLinearSectionContainment

variable {X : Scheme.{u}} (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
  (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
  (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- The actual original exterior map is onto for every retained
normalization of the given genuine complete system. -/
theorem normalized_lambda_three_surjective
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (n : NormalizedEvaluation K f E)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hg : genus f = 9) : Function.Surjective (ExteriorEvaluation.lambda K f E 3) := by
  letI := isIso_globalSections_of_isAlgClosed K f
  exact MukaiExteriorEvaluationSurjectivity.lambda_three_surjective K f E
    n.basis n.diagram n.relation hsemi c hg

/-- The genuine original normalized LG morphism is a closed immersion;
there is no exterior-surjectivity or embedding premise. -/
theorem normalized_map_isClosedImmersion
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (n : NormalizedEvaluation K f E)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    IsClosedImmersion n.diagram.map :=
  MukaiLagrangianClosedImmersion.normalized_map_isClosedImmersion K f E c n hnp
    (normalized_lambda_three_surjective K f E c n hsemi hg)

/-- Actual bundle geometry constructs the normalization, defining
matrix, and closed immersion into the original incidence fibre. -/
theorem exists_closed_fibre_lift
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : finrank K (H0 K f E) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (n : NormalizedEvaluation K f E) (M : Matrix (Fin 5) (Fin 14) K)
      (hM : Function.Surjective M.mulVec)
      (q : X ⟶ LagrangianFibreFactorization.fibre K
        (LagrangianMatrixPointRows.matrixPoint K M hM)),
      IsClosedImmersion q ∧
      q ≫ LagrangianFibreFactorization.fibreToLG K
          (LagrangianMatrixPointRows.matrixPoint K M hM) = n.diagram.map ∧
      q ≫ pullback.fst (LagrangianMatrixPointRows.matrixPoint K M hM)
          (LagrangianLinearSections.familyProjection K) = f := by
  obtain ⟨n, M, hM, q, hq, hbase⟩ :=
    exists_incidence_fibre_lift K f E c hg hgen h6 hsemi
  have hLambda := normalized_lambda_three_surjective K f E c n hsemi hg
  exact MukaiLagrangianClosedImmersion.exists_closed_fibre_lift K f E c hg
    hgen h6 hsemi hnp hLambda

end M9Native.MukaiActualLagrangianClosedImmersion

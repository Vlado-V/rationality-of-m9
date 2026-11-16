module

public import M9StacksIntegration.MukaiCurveConormalIsomorphism
public import M9StacksIntegration.LagrangianFibreRecognitionCriterion

@[expose] public section

/-!
# The original nonpentagonal Mukai curve is its entire original linear section

The actual bundle produces the normalization, defining rows and closed
incidence lift. The geometric conormal theorem proves the original row
map invertible, and the actual full-zero/connected-fibre argument proves
that lift is an isomorphism. Every map is the original one; the LG and
base triangles are retained. No fibre smoothness, conormal generation,
connectedness, rank witness or fibre-isomorphism premise is supplied.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.MukaiActualLinearSectionRecognition

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation

variable {X : Scheme.{u}} (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
  (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
  (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- Every genuine normalized original incidence lift is already an
isomorphism onto its entire original scheme-theoretic fibre. -/
theorem normalized_fibreLift_isIso
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (n : NormalizedEvaluation K f E)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hg : genus f = 9)
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
    (q : X ⟶ LagrangianFibreFactorization.fibre K
      (LagrangianMatrixPointRows.matrixPoint K M hM))
    (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
      (LagrangianMatrixPointRows.matrixPoint K M hM) = n.diagram.map)
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    IsIso q := by
  letI := MukaiActualLagrangianClosedImmersion.normalized_map_isClosedImmersion
    K f E c n hsemi hg hnp
  let p := LagrangianMatrixPointRows.matrixPoint K M hM
  have hp : p ≫ LagrangianLinearSections.parameterProjection K = 𝟙 _ :=
    SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM
  letI := MukaiLagrangianClosedImmersion.fibreToLG_isClosedImmersion K p hp
  letI : IsClosedImmersion (q ≫ LagrangianFibreFactorization.fibreToLG K p) := by
    rw [hq]
    infer_instance
  letI : IsClosedImmersion q := IsClosedImmersion.of_comp_isClosedImmersion q
    (LagrangianFibreFactorization.fibreToLG K p)
  letI := MukaiCurveConormalIsomorphism.normalized_sequenceMap_isIso
    K f E c n hsemi hg M hM q hq hnp
  exact LagrangianFibreRecognitionCriterion.isIso_fibreLift_of_isIso_sequenceMap
    K M hM n.diagram.map q hq

/-- The genuine canonical generated complete Semi bundle constructs the
normalization, the original defining matrix, and an actual isomorphism
to the ENTIRE original incidence fibre, retaining both original maps. -/
theorem exists_fibreIso
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : finrank K (H0 K f E) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (n : NormalizedEvaluation K f E) (M : Matrix (Fin 5) (Fin 14) K)
      (hM : Function.Surjective M.mulVec)
      (e : X ≅ LagrangianFibreFactorization.fibre K
        (LagrangianMatrixPointRows.matrixPoint K M hM)),
      e.hom ≫ LagrangianFibreFactorization.fibreToLG K
        (LagrangianMatrixPointRows.matrixPoint K M hM) = n.diagram.map ∧
      e.hom ≫ pullback.fst (LagrangianMatrixPointRows.matrixPoint K M hM)
        (LagrangianLinearSections.familyProjection K) = f := by
  obtain ⟨n,M,hM,q,hqclosed,hq,hbase⟩ :=
    MukaiActualLagrangianClosedImmersion.exists_closed_fibre_lift K f E c hg hgen h6 hsemi hnp
  letI := normalized_fibreLift_isIso K f E c n hsemi hg M hM q hq hnp
  exact ⟨n,M,hM,asIso q,hq,hbase⟩

end M9Native.MukaiActualLinearSectionRecognition

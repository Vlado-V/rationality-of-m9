module

public import M9StacksIntegration.MukaiConormalGenericRank
public import M9StacksIntegration.MukaiConormalCurveJetRank
public import M9StacksIntegration.MukaiCanonicalGenericDifferential
public import M9StacksIntegration.LagrangianConormalRank

@[expose] public section

/-! Actual third-exterior evaluation is onto for the original canonical
genus-nine semi-irreducible bundle. The cubic proves generic conormal
rank seven; genuine curve jets give rank at most six under failure of
surjectivity. Legacy visibility is inherited from the frozen rank-locus
providers; no surjectivity or conormal-rank conclusion is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiExteriorEvaluationSurjectivity

open MukaiCubicCurveKernel MukaiPrimitiveCanonicalEvaluation MukaiConormalGenericRank

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0)) (d : EvaluationDiagram K f E b)

include d in
theorem primitiveEvaluation_surjective
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) : Function.Surjective (primitiveEvaluation K f E b) := by
  by_contra hD
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  let : JacobsonSpace X := ClosedPointCurveRank.jacobsonSpace_of_curve K f
  let := determinantH0_finite K f E
  let Ω := Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Ω 6 :=
    LagrangianDegree.lagrangianDifferentials_rank K
  have hΩ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback d.map).obj Ω) 6 :=
    isFiniteLocallyFreeOfRank_pullback d.map Ω 6
  have hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials f) 1 := CurveTangentLineGeometry.differentials_rank_one f
  let δ := Scheme.Hom.relativeDifferentialsMap d.map (LagrangianGrassmannian.projection K)
    f (𝟙 _) (by simpa using d.over_base)
  have hδ : MukaiSemiIrreducible.mapRankAt δ (genericPoint X) = 1 :=
    MukaiCanonicalGenericDifferential.evaluationDiagram_differential_rank_one K f E c hg b d
  have hbound := MukaiGenericRankBound.bound_of_closed_rank_one_locus
    (curveEvaluationMap K f E b d) δ 7 (finrank K (DeterminantH0 K f E)) 6 1 6
    (curveSource_rank K f E b d)
    (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E))) hΩ hC hδ
    (MukaiConormalCurveJetRank.closed_rank_le_six_of_not_surjective K f E c hg b d hD)
  have hlo := generic_rank_seven K f E b d hσ hsemi c hg
  have hhi := hbound (genericPoint X)
  omega

include d in
/-- This is the original native exterior-evaluation map on actual
zeroth cohomology, rather than its coordinate surrogate. -/
theorem lambda_three_surjective
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) : Function.Surjective (ExteriorEvaluation.lambda K f E 3) := by
  have honto : Function.Surjective (lambdaThree K f E b) := by
    apply LinearMap.range_eq_top.mp
    rw [← range_primitiveEvaluation K f E b hσ]
    exact LinearMap.range_eq_top.mpr (primitiveEvaluation_surjective K f E b d hσ hsemi c hg)
  intro s
  obtain ⟨w,hw⟩ := honto s
  exact ⟨exteriorPower.map 3 b.equivFun.symm.toLinearMap w,hw⟩

end M9Native.MukaiExteriorEvaluationSurjectivity

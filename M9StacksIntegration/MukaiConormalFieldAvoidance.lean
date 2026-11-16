module

public import M9StacksIntegration.MukaiEvaluationPointFrame
public import M9StacksIntegration.MukaiSchubertTransport
public import M9StacksIntegration.FieldPointMapRankConsequences
public import M9StacksIntegration.MukaiCurveEvaluationPoint
public import M9StacksIntegration.MukaiConormalNormalization

/-! Actual Semi3 excludes singular conormal forms at genuine same-base
field points. Both the conormal image and the original complete
evaluation are normalized by the same constructed symplectic frame. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.MukaiConormalFieldAvoidance

open LagrangianField LagrangianTransitivity LagrangianMatrixChart
open MukaiPrimitiveCanonicalEvaluation MukaiQuarticGradientTransport MukaiConormalPrimitive
open MukaiEvaluationPointFrame MukaiSchubertTransport MukaiCubicCurveKernel

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of K)) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

theorem discriminant_ne_zero_of_evaluation_kernel
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (g : Matrix.symplecticGroup (Fin 3) K)
    (e : (Scheme.Modules.pullback p).obj E ≅ freeOn (Spec (.of K)) 3)
    (hM : (AlgebraicGeometry.Grassmannian.pullbackFreeIso p 6).inv ≫
      (Scheme.Modules.pullback p).map (MukaiSemiIrreducible.evaluation K f E b) ≫ e.hom =
      Stacks.FreeSheafMatrix.ofMatrix ((standardQuotient K * matrixSix K g).map
        (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom))
    (v : MukaiConormalPencil.ConormalCoordinates K) (hv : v ≠ 0)
    (hker : primitiveEvaluation K f E b (formsAction K g⁻¹ (conormalForm K v)) = 0) :
    v.2.val.det ≠ 0 := by
  intro hdet
  obtain ⟨s,hs,hclass,hr⟩ := MukaiSchubertTransport.exists_independent_triple_of_discriminant_zero
    K g v hv hdet
  let t : Fin 3 → cohomologyOverField K f E 0 := fun i => b.equivFun.symm (s i)
  have ht : LinearIndependent K t := hs.map' b.equivFun.symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr b.equivFun.symm.injective)
  have hw : ExteriorEvaluation.lambda K f E 3 (exteriorPower.ιMulti K 3 t) = 0 := by
    rw [← lambdaThree_ιMulti K f E b s,
      ← MukaiConormalClosedPoint.primitiveEvaluation_primitiveClass K f E b hσ, hclass]
    exact hker
  have hcol : ((standardQuotient K * matrixSix K g) *
      LagrangianUniversalTriples.columnMatrix K s).col =
      (fun i => MukaiSchubertCone.firstProjection K ((matrixSix K g).mulVec (s i))) := by
    funext i
    change (standardQuotient K * matrixSix K g).mulVec (s i) = _
    rw [← Matrix.mulVec_mulVec]
    exact LinearMap.congr_fun (MukaiConormalNormalization.standardProjection_eq K) _
  have hm : ((standardQuotient K * matrixSix K g) *
      LagrangianUniversalTriples.columnMatrix K s).rank ≤ 1 := by
    rw [Matrix.rank_eq_finrank_span_cols, hcol]
    exact hr
  have hframe := triple_point_frame K f E b p hp e (standardQuotient K * matrixSix K g) hM s
  have hrank := FieldPointMapRankConsequences.mapRankAt_of_point_frame K
    (MukaiSemiIrreducible.evaluation K f E t) p e
    ((standardQuotient K * matrixSix K g) * LagrangianUniversalTriples.columnMatrix K s) hframe
  have hbad : MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation K f E t)
      (p (SpecFieldStalkSections.point K)) ≤ 1 := hrank.le.trans hm
  exact MukaiSchubertAvoidance.lambda_three_ne_zero_of_rankAt_le_one K f E hsemi t ht
    (p (SpecFieldStalkSections.point K)) hbad hw

variable [IsProper f]

/-- Semi3 derives the genuine pointwise rank lower bound for the
original conormal-to-determinant-evaluation sheaf map. -/
theorem six_le_mapRankAt (hσ : ExteriorEvaluation.lambda K f E 2
    (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    6 ≤ MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d)
      (p (SpecFieldStalkSections.point K)) := by
  obtain ⟨g,e,_hg,hM,himage⟩ := exists_simultaneous_normal_form K f E b d p hp
  let T := (formsAction K g⁻¹).toLinearMap.comp (conormalForm K)
  let D := (primitiveEvaluation K f E b).comp T
  have hk : finrank K (LinearMap.ker D) ≤ 1 := by
    apply MukaiConormalPencil.finrank_le_one_of_det_ne_zero
      (LinearMap.ker D) MukaiConormalPencil.matrixProjection
    intro v hv hne
    exact discriminant_ne_zero_of_evaluation_kernel K f E b hσ hsemi p hp g e hM v hne hv
  have hrange : LinearMap.range ((primitiveEvaluation K f E b).comp
      (MukaiCurvePointCoordinates.pointFormsMap K f E b d p)) = LinearMap.range D := by
    rw [LinearMap.range_comp, himage, ← LinearMap.range_comp]
  rw [MukaiCurveEvaluationPoint.mapRankAt_eq_finrank_evaluation K f p hp E b d, hrange]
  have hd := D.finrank_range_add_finrank_ker
  rw [MukaiConormalPencil.finrank_conormalCoordinates] at hd
  omega

end M9Native.MukaiConormalFieldAvoidance

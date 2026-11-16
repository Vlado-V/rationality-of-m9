module

public import M9StacksIntegration.MukaiCurveJetCotangentRank
public import M9StacksIntegration.MukaiCurveEvaluationPoint
public import M9StacksIntegration.MukaiKernelIntersection
public import M9StacksIntegration.MukaiPrimitiveCanonicalDiagram
public import M9StacksIntegration.LagrangianTranslatedDeterminantSections
public import M9StacksIntegration.BaseFieldPoints

/-!
# The actual local conormal-evaluation rank from genuine curve jets

At a closed point where the original curve-to-LG differential has rank
one, failure of the original primitive evaluation to be onto forces
rank at most six for the original conormal evaluation. The two-dimensional
curve jet is proved onto on an actual translated-chart pullback.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.MukaiConormalCurveJetRank

open MukaiPrimitiveCanonicalEvaluation MukaiCubicCurveKernel MukaiCurvePointCoordinates
open MukaiEvaluationCurveJetFrames MukaiEvaluationCurveJetChainRule
open LagrangianGrassmannian LagrangianTranslatedCharts LagrangianTranslatedDeterminantSections

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9)

include c hg in
omit [CharZero K] [IsAlgClosed K] [Smooth f]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3] in
/-- The actual canonical determinant comparison gives the actual
nine-dimensional target of the original primitive evaluation. -/
theorem determinantH0_finrank_nine :
    finrank K (DeterminantH0 K f E) = 9 :=
  (cohomologyOverFieldIso K f c 0).toLinearEquiv.finrank_eq.trans
    ((Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le).trans hg)

variable (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

include c hg in
/-- The original field-point conormal evaluation has rank at most six.
No curve-jet surjectivity or conormal-image comparison is assumed. -/
theorem point_rank_le_six_of_not_surjective
    (hD : ¬ Function.Surjective (primitiveEvaluation K f E b))
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hr : MukaiSemiIrreducible.mapRankAt
      (Scheme.Hom.relativeDifferentialsMap d.map (projection K) f (𝟙 _)
        (by simpa using d.over_base)) (p (SpecFieldStalkSections.point K)) = 1) :
    MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d)
      (p (SpecFieldStalkSections.point K)) ≤ 6 := by
  have hpLG : (p ≫ d.map) ≫ projection K = 𝟙 _ := by
    rw [Category.assoc, d.over_base, hp]
  obtain ⟨g,z₀,hz₀⟩ := exists_translatedBigCell_point K (p ≫ d.map) hpLG
  let h := translatedBigCell K g
  let Y := pullback d.map h
  let u : Y ⟶ X := pullback.fst d.map h
  let γ : Y ⟶ MukaiConormalChartJets.chart K := pullback.snd d.map h
  let : IsOpenImmersion h := by dsimp [h]; infer_instance
  let : IsOpenImmersion u := by dsimp [u]; infer_instance
  let : Etale h := inferInstance
  let : Etale u := inferInstance
  have hh : h ≫ projection K = MukaiConormalChartJets.chartProjection K :=
    translatedBigCell_projection K g
  have hfactor : γ ≫ h = u ≫ d.map := (pullback.condition (f := d.map) (g := h)).symm
  let z : Spec (.of K) ⟶ Y := pullback.lift p z₀ hz₀.symm
  have hzu : z ≫ u = p := pullback.lift_fst _ _ _
  have hγ : γ ≫ MukaiConormalChartJets.chartProjection K = u ≫ f :=
    gamma_overBase K f E b d u h γ hfactor hh
  have hzq : z ≫ (u ≫ f) = 𝟙 _ := by rw [← Category.assoc, hzu, hp]
  have hzChart : (z ≫ γ) ≫ MukaiConormalChartJets.chartProjection K = 𝟙 _ := by
    rw [Category.assoc, hγ, hzq]
  let eChart := translatedDeterminantIso K g
  let e := eCurve K f E b d u h γ hfactor eChart
  let J₀ := MukaiEvaluationCurveJets.curveJet K (u ≫ f) z
    (MukaiEvaluationCurveJets.framedSections K f E b u e)
  let JChart := MukaiConormalChartJets.firstJetMap K (z ≫ γ)
    (MukaiConormalChartFrame.sectionTuple K h eChart)
  have hchain : J₀ = (jetTargetMap K (u ≫ f) γ hγ z).comp JChart :=
    curveJet_framedSections_eCurve K f E b d u h γ hfactor eChart hh z
  have hr' : MukaiSemiIrreducible.mapRankAt
      (MukaiCurveJetCotangentRank.originalDifferential K f d.map d.over_base)
      ((z ≫ u) (SpecFieldStalkSections.point K)) = 1 := by
    simpa only [hzu, MukaiCurveJetCotangentRank.originalDifferential] using hr
  have hcot := MukaiCurveJetCotangentRank.pointCotangentMap_surjective_of_rank_one
    K f u d.map d.over_base h hh γ hγ hfactor z hr'
  have htarget : Function.Surjective (jetTargetMap K (u ≫ f) γ hγ z) := by
    rintro ⟨a,t⟩
    obtain ⟨s,hs⟩ := hcot t
    refine ⟨(a,s), ?_⟩
    exact Prod.ext rfl hs
  have hchart : Function.Surjective JChart :=
    MukaiConormalChartJetRank.firstJetMap_surjective K h hh (z ≫ γ) eChart
  have hJ₀ : Function.Surjective J₀ := by
    rw [hchain]
    exact htarget.comp hchart
  obtain ⟨hfinite,hdim⟩ := MukaiCurveJetCotangentRank.pointCotangent_finite_and_finrank K f u z
  let := hfinite
  let eT : MukaiEvaluationCurveJets.PointCotangent K (u ≫ f) z ≃ₗ[K] K :=
    LinearEquiv.ofFinrankEq _ _ (hdim.trans (Module.finrank_self K).symm)
  let eJet := (LinearEquiv.refl K K).prodCongr eT
  let J := eJet.toLinearMap.comp J₀
  have hJ : Function.Surjective J := eJet.surjective.comp hJ₀
  let P := pointFormsMap K f E b d p
  let A := LinearMap.range P
  have hA : finrank K A = 7 := finrank_range_pointFormsMap K f E b d p
  have hpoint : ((z ≫ γ) ≫ h) = p ≫ d.map := by
    calc
      _ = z ≫ (γ ≫ h) := Category.assoc _ _ _
      _ = z ≫ (u ≫ d.map) := congrArg (fun t => z ≫ t) hfactor
      _ = (z ≫ u) ≫ d.map := (Category.assoc _ _ _).symm
      _ = p ≫ d.map := congrArg (fun t => t ≫ d.map) hzu
  have hAforms : A = LinearMap.range
      (MukaiConormalFieldCoordinates.formsMap K ((z ≫ γ) ≫ h)) := by
    rw [hpoint]
    change LinearMap.range (pointFormsMap K f E b d p) = _
    rw [pointFormsMap_eq]
    exact LinearMap.range_comp_of_range_eq_top _ (sourcePointEquiv K f E b d p).range
  have hAChart : A ≤ LinearMap.ker JChart := by
    rw [hAforms]
    exact (MukaiConormalChartImage.range_formsMap_eq_ker_firstJetMap
      K h hh (z ≫ γ) hzChart eChart).le
  have hAJ : A ≤ LinearMap.ker J := by
    intro ell hell
    have hzC : JChart ell = 0 := hAChart hell
    change eJet (J₀ ell) = 0
    rw [hchain]
    change eJet (jetTargetMap K (u ≫ f) γ hγ z (JChart ell)) = 0
    simp only [hzC, map_zero]
  have hDJ : LinearMap.ker (primitiveEvaluation K f E b) ≤ LinearMap.ker J := by
    intro ell hell
    have hzC : J₀ ell = 0 :=
      MukaiEvaluationCurveJets.ker_primitiveEvaluation_le_ker_curveJet
        K f E b u e z hzq hell
    change eJet (J₀ ell) = 0
    exact (congrArg eJet hzC).trans eJet.map_zero
  let := determinantH0_finite K f E
  have hres := MukaiKernelIntersection.restriction_rank_le_six
    (primitiveEvaluation K f E b) J (MukaiPrimitiveCanonicalDiagram.primitive_coordinate_finrank K)
    (determinantH0_finrank_nine K f E c hg) hD hJ A hA hAJ hDJ
  calc
    _ = finrank K (LinearMap.range ((primitiveEvaluation K f E b).comp P)) :=
      MukaiCurveEvaluationPoint.mapRankAt_eq_finrank_evaluation K f p hp E b d
    _ = finrank K (LinearMap.range ((primitiveEvaluation K f E b).comp A.subtype)) := by
      apply congrArg (fun S : Submodule K (DeterminantH0 K f E) => finrank K S)
      simp only [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    _ ≤ 6 := hres

include c hg in
/-- The actual closed-point local rank bound used in the global cubic
argument, with the original native differential and original evaluation. -/
theorem closed_rank_le_six_of_not_surjective
    (hD : ¬ Function.Surjective (primitiveEvaluation K f E b))
    (x : X) (hx : IsClosed ({x} : Set X))
    (hr : MukaiSemiIrreducible.mapRankAt
      (Scheme.Hom.relativeDifferentialsMap d.map (projection K) f (𝟙 _)
        (by simpa using d.over_base)) x = 1) :
    MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) x ≤ 6 := by
  let p := pointOfClosedPoint f x hx
  have hr' : MukaiSemiIrreducible.mapRankAt
      (Scheme.Hom.relativeDifferentialsMap d.map (projection K) f (𝟙 _)
        (by simpa using d.over_base)) (p (SpecFieldStalkSections.point K)) = 1 := by
    simpa only [p, pointOfClosedPoint_apply] using hr
  simpa only [p, pointOfClosedPoint_apply] using
    point_rank_le_six_of_not_surjective K f E c hg b d hD p
      (pointOfClosedPoint_comp f x hx) hr'

end M9Native.MukaiConormalCurveJetRank

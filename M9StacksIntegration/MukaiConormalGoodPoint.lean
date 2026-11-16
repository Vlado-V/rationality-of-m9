module

public import M9StacksIntegration.MukaiConormalGenericRank
public import M9StacksIntegration.MukaiConormalNativeCovariance
public import M9StacksIntegration.MukaiCurveEvaluationPoint
public import M9StacksIntegration.MukaiPrimitiveCanonicalDiagram
public import M9StacksIntegration.BaseFieldPoints

@[expose] public section

/-!
# An actual rational point where the original full LG jets separate relations

The genuine curve-kernel argument supplies a closed point of rank seven.
The original algebraically closed field converts it to an actual rational
point over the identity base map. Rank-nullity proves injectivity on the
actual seven-dimensional conormal source. The proved native full-LG jet
image theorem then gives a translated chart where a primitive relation
and a vanishing full LG first jet force the original form to be zero.

This leaf retains the frozen rank producer's legacy visibility. No rank,
good-point, jet-image, or conormal-map-isomorphism premise is supplied.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.MukaiConormalGoodPoint

open MukaiPrimitiveCanonicalEvaluation MukaiCubicCurveKernel MukaiCurvePointCoordinates
open LagrangianGrassmannian LagrangianTranslatedCharts

private theorem injective_of_full_range {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] (a : V →ₗ[K] W)
    (h : finrank K (LinearMap.range a) = finrank K V) : Function.Injective a := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have hn := a.finrank_range_add_finrank_ker
  omega

private theorem injective_of_comp_equiv {K T V W : Type*} [Field K]
    [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (a : V →ₗ[K] W) (e : T ≃ₗ[K] V)
    (h : Function.Injective (a.comp e.toLinearMap)) : Function.Injective a := by
  intro x y hxy
  apply e.symm.injective
  apply h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hxy

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
  (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
  (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
  (n : NormalizedEvaluation K f E)
  (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
  (hg : genus f = 9)

include c hsemi hg

/-- An actual original rational point makes the original seven-source
primitive evaluation injective. The rank witness is derived internally. -/
theorem exists_rational_injective_point :
    ∃ p : Spec (.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      Function.Injective ((primitiveEvaluation K f E n.basis).comp
        (pointFormsMap K f E n.basis n.diagram p)) := by
  letI := isIso_globalSections_of_isAlgClosed K f
  obtain ⟨x,hx,hr⟩ := MukaiConormalGenericRank.exists_closed_full_rank
    K f E n.basis n.diagram n.relation hsemi c hg
  let p := pointOfClosedPoint f x hx
  have hp : p ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
  have hrp : MukaiSemiIrreducible.mapRankAt
      (curveEvaluationMap K f E n.basis n.diagram) (p (SpecFieldStalkSections.point K)) = 7 := by
    simpa only [p, pointOfClosedPoint_apply] using hr
  obtain ⟨hfinite,hdim⟩ := pointSource_finite_and_finrank K f E n.basis n.diagram p
  letI := hfinite
  refine ⟨p,hp,injective_of_full_range _ ?_⟩
  exact (MukaiCurveEvaluationPoint.mapRankAt_eq_finrank_evaluation
    K f p hp E n.basis n.diagram).symm.trans (hrp.trans hdim.symm)

/-- On an actual translated chart through a genuine good rational
point, the two actual native kernels have trivial intersection.
The first jet is the FULL LG value-and-cotangent jet. -/
theorem exists_translated_relation_separating_point :
    ∃ (p : Spec (.of K) ⟶ X) (g : Matrix.symplecticGroup (Fin 3) K)
      (z : Spec (.of K) ⟶ MukaiConormalChartJets.chart K),
      p ≫ f = 𝟙 _ ∧ z ≫ translatedBigCell K g = p ≫ n.diagram.map ∧
      z ≫ MukaiConormalChartJets.chartProjection K = 𝟙 _ ∧
      ∀ ell : MukaiPrimitiveQuartic.Forms K,
        primitiveEvaluation K f E n.basis ell = 0 →
        MukaiConormalChartJets.firstJetMap K z
          (MukaiConormalChartCovariance.sectionTuple K g) ell = 0 → ell = 0 := by
  obtain ⟨p,hp,hpI⟩ := exists_rational_injective_point K f E c n hsemi hg
  have hpLG : (p ≫ n.diagram.map) ≫ projection K = 𝟙 _ := by
    rw [Category.assoc, n.diagram.over_base, hp]
  obtain ⟨g,z,hzg,hz⟩ :=
    LagrangianRationalTranslatedPoint.exists_rational_chart K (p ≫ n.diagram.map) hpLG
  have hI : Function.Injective ((primitiveEvaluation K f E n.basis).comp
      (MukaiConormalFieldCoordinates.formsMap K (p ≫ n.diagram.map))) := by
    apply injective_of_comp_equiv _ (sourcePointEquiv K f E n.basis n.diagram p)
    simpa only [pointFormsMap_eq, LinearMap.comp_assoc] using hpI
  have hIz : Function.Injective ((primitiveEvaluation K f E n.basis).comp
      (MukaiConormalFieldCoordinates.formsMap K (z ≫ translatedBigCell K g))) := by
    rw [hzg]
    exact hI
  refine ⟨p,g,z,hp,hzg,hz,?_⟩
  intro ell hμ hJ
  have hmem : ell ∈ LinearMap.range
      (MukaiConormalFieldCoordinates.formsMap K (z ≫ translatedBigCell K g)) := by
    rw [MukaiConormalNativeCovariance.translated_range K z hz g]
    exact hJ
  obtain ⟨a,ha⟩ := hmem
  have ha0 : a = 0 := hIz (by
    change primitiveEvaluation K f E n.basis
      (MukaiConormalFieldCoordinates.formsMap K (z ≫ translatedBigCell K g) a) =
      primitiveEvaluation K f E n.basis
        (MukaiConormalFieldCoordinates.formsMap K (z ≫ translatedBigCell K g) 0)
    rw [ha, hμ, map_zero, map_zero])
  calc
    ell = MukaiConormalFieldCoordinates.formsMap K (z ≫ translatedBigCell K g) a := ha.symm
    _ = 0 := by rw [ha0, map_zero]

end M9Native.MukaiConormalGoodPoint

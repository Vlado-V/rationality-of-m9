module

public import M9StacksIntegration.MukaiEvaluationCurveJets
public import M9StacksIntegration.MukaiConormalChartJets
public import M9StacksIntegration.LineFramePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap

/-!
# The actual value-and-differential chain rule from a chart to the curve

The cotangent point map is the original relative differential, pulled
back to the original Spec-field point, with the actual pullbackComp
comparison retained. Arbitrary actual chart sections satisfy the jet
identity; no jet or kernel comparison is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.MukaiEvaluationCurveJetChainRule

variable (K : Type u) [Field K] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (.of K)) (γ : Y ⟶ MukaiConormalChartJets.chart K)
  (hγ : γ ≫ MukaiConormalChartJets.chartProjection K = q)

/-- The actual original relative differential of the given base square. -/
def cotangentDifferential :=
  Scheme.Hom.relativeDifferentialsMap γ (MukaiConormalChartJets.chartProjection K) q
    (𝟙 _) (by simpa using hγ)

/-- The actual pulled cotangent map on original Spec-field global
sections, with the inverse pullback-composition comparison explicit. -/
def pointCotangentMap (z : Spec (.of K) ⟶ Y) :
    MukaiConormalChartJets.PointCotangent K (z ≫ γ) →ₗ[K]
      MukaiEvaluationCurveJets.PointCotangent K q z :=
  (moduleSpecΓFunctor.map
    (((Scheme.Modules.pullbackComp z γ).inv.app (MukaiConormalChartJets.chartCotangent K)) ≫
      (Scheme.Modules.pullback z).map (cotangentDifferential K q γ hγ))).hom

/-- The adjunction defining pullback acts on actual pulled global
sections by the actual module morphism. -/
theorem adjoint_globalSections {A B : Scheme.{u}} (g : A ⟶ B)
    (M : B.Modules) (N : A.Modules) (a : (Scheme.Modules.pullback g).obj M ⟶ N)
    (s : Γ(M, ⊤)) :
    a.app ⊤ (pullbackGlobalSections g M s) =
      (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N a).app ⊤) s := by
  rw [SectionsEqualizer.pullbackGlobalSections_unit, Adjunction.homEquiv_apply]
  change a.app ⊤ (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ s) =
    a.app (g ⁻¹ᵁ ⊤) (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ s)
  exact (SectionsEqualizer.moduleHom_app_preimage_top g a _).symm

/-- The actual universal derivative of a pulled function is the image
of its original derivative under the original relative differential. -/
theorem differential_pullbackGlobalSections (s : Γ(MukaiConormalChartJets.chart K, ⊤)) :
    (cotangentDifferential K q γ hγ).app ⊤
      (pullbackGlobalSections γ (MukaiConormalChartJets.chartCotangent K)
        ((Scheme.Hom.universalRelativeDerivation (MukaiConormalChartJets.chartProjection K)).d s)) =
      (Scheme.Hom.universalRelativeDerivation q).d (γ.appTop s) :=
  (adjoint_globalSections γ _ _ (cotangentDifferential K q γ hγ) _).trans
    (Scheme.Hom.relativeDifferentialsMap_app_d
      (f := γ) (p := MukaiConormalChartJets.chartProjection K) (p' := q)
      (𝟙 _) (by simpa using hγ) ⊤ s)

/-- The genuine cotangent point map sends each actual chart derivative
to the actual derivative of its pulled function. -/
theorem pointCotangentMap_derivative (z : Spec (.of K) ⟶ Y)
    (s : Γ(MukaiConormalChartJets.chart K, ⊤)) :
    pointCotangentMap K q γ hγ z (MukaiConormalChartJets.derivative K (z ≫ γ) s) =
      MukaiEvaluationCurveJets.curveDerivative K q z (γ.appTop s) := by
  change ((Scheme.Modules.pullback z).map (cotangentDifferential K q γ hγ)).app ⊤
      (((Scheme.Modules.pullbackComp z γ).inv.app (MukaiConormalChartJets.chartCotangent K)).app ⊤
        (pullbackGlobalSections (z ≫ γ) (MukaiConormalChartJets.chartCotangent K)
          ((Scheme.Hom.universalRelativeDerivation (MukaiConormalChartJets.chartProjection K)).d s))) = _
  rw [LineFramePullback.pullbackComp_inv_apply,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
    differential_pullbackGlobalSections]
  rfl

variable [CharZero K]

/-- The actual scalar-section pullback of the fourteen chart sections. -/
def pullbackTuple (v : Fin 14 → Γ(MukaiConormalChartJets.chart K, ⊤)) : Fin 14 → Γ(Y, ⊤) :=
  fun j => γ.appTop (v j)

/-- The actual identity on values and genuine differential on the
original cotangent factors. -/
def jetTargetMap (z : Spec (.of K) ⟶ Y) :
    K × MukaiConormalChartJets.PointCotangent K (z ≫ γ) →ₗ[K]
      K × MukaiEvaluationCurveJets.PointCotangent K q z :=
  (LinearMap.id : K →ₗ[K] K).prodMap (pointCotangentMap K q γ hγ z)

/-- Actual value-and-differential jets satisfy the chain rule, with
their original native sheaves and pullback-composition comparison. -/
theorem curveJet_pullbackTuple (z : Spec (.of K) ⟶ Y)
    (v : Fin 14 → Γ(MukaiConormalChartJets.chart K, ⊤)) :
    MukaiEvaluationCurveJets.curveJet K q z (pullbackTuple K γ v) =
      (jetTargetMap K q γ hγ z).comp (MukaiConormalChartJets.firstJetMap K (z ≫ γ) v) := by
  apply LinearMap.ext
  intro ell
  apply Prod.ext
  · change (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) *
        (Scheme.ΓSpecIso (.of K)).hom (z.appTop (γ.appTop (v j)))) =
      ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) *
        MukaiConormalChartJets.value K (z ≫ γ) (v j)
    rfl
  · change (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) •
        MukaiEvaluationCurveJets.curveDerivative K q z (γ.appTop (v j))) =
      pointCotangentMap K q γ hγ z
        (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) •
          MukaiConormalChartJets.derivative K (z ≫ γ) (v j))
    simp only [map_sum, map_smul, pointCotangentMap_derivative]

end M9Native.MukaiEvaluationCurveJetChainRule

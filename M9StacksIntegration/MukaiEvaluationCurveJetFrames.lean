module

public import M9StacksIntegration.MukaiEvaluationCurveJetChainRule
public import M9StacksIntegration.MukaiConormalChartFrame

/-!
# Actual determinant frames and the curve/chart jet chain rule

The curve frame is constructed from the original evaluation diagram's
determinant isomorphism and the genuine pullback square. Its fourteen
sections are therefore the actual pulled chart sections, without a
separate frame-compatibility hypothesis.
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
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.MukaiEvaluationCurveJetFrames

open MukaiPrimitiveCanonicalEvaluation LagrangianPluckerQuotient

variable (K : Type u) [Field K] [CharZero K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)
    (u : Y ⟶ X) (h : MukaiConormalChartJets.chart K ⟶ LagrangianGrassmannian.space K)
    (γ : Y ⟶ MukaiConormalChartJets.chart K)
    (hfactor : γ ≫ h = u ≫ d.map)
    (eChart : (Scheme.Modules.pullback h).obj (determinantLine K) ≅
      SheafOfModules.unit (MukaiConormalChartJets.chart K).ringCatSheaf)

/-- The actual curve determinant frame, using the original determinant
comparison, both pullback-composition maps, and the original square. -/
def eCurve : (Scheme.Modules.pullback u).obj (Scheme.Modules.exteriorPower E (3 : ℤ)) ≅
    MukaiBundle.structureModule Y :=
  ((Scheme.Modules.pullback u).mapIso (d.determinantIso K f E)).symm ≪≫
    LineFramePullback.squareFrame u d.map γ h hfactor.symm (determinantLine K) eChart

/-- Inverting the genuine determinant comparison recovers each original
primitive section, rather than a chosen section with the same value. -/
theorem determinantIso_inv_section (j : Fin 14) :
    (d.determinantIso K f E).inv.app ⊤ (determinantSections K f E b j) =
      pullbackGlobalSections d.map (determinantLine K) (primitiveSections K j) := by
  have hd := d.primitiveCoordinates K f E j
  change (d.determinantIso K f E).hom.app ⊤
    (pullbackGlobalSections d.map (determinantLine K) (primitiveSections K j)) =
      determinantSections K f E b j at hd
  exact (congrArg ((d.determinantIso K f E).inv.app ⊤) hd.symm).trans
    (SectionsEqualizer.moduleIso_hom_inv_app (d.determinantIso K f E).symm _)

/-- The constructed curve frame has exactly the original chart tuple
as its pulled coordinate sections. -/
theorem framedSections_eCurve (j : Fin 14) :
    MukaiEvaluationCurveJets.framedSections K f E b u
        (eCurve K f E b d u h γ hfactor eChart) j =
      γ.appTop (MukaiConormalChartFrame.sectionTuple K h eChart j) := by
  change (LineFramePullback.squareFrame u d.map γ h hfactor.symm (determinantLine K)
      eChart).hom.app ⊤
    (((Scheme.Modules.pullback u).map (d.determinantIso K f E).inv).app ⊤
      (pullbackGlobalSections u (Scheme.Modules.exteriorPower E (3 : ℤ))
        (determinantSections K f E b j))) = _
  rw [SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
    determinantIso_inv_section]
  change LinearIncidenceTensorCoordinates.unitCoordinate Y
    ((LineFramePullback.squareFrame u d.map γ h hfactor.symm (determinantLine K)
      eChart).hom.app ⊤
      (pullbackGlobalSections u ((Scheme.Modules.pullback d.map).obj (determinantLine K))
        (pullbackGlobalSections d.map (determinantLine K) (primitiveSections K j)))) =
      γ.appTop (LinearIncidenceTensorCoordinates.unitCoordinate (MukaiConormalChartJets.chart K)
        (eChart.hom.app ⊤ (pullbackGlobalSections h (determinantLine K) (primitiveSections K j))))
  exact LineFramePullback.squareFrame_coordinate u d.map γ h hfactor.symm
    (determinantLine K) eChart (primitiveSections K j)

/-- The fourteen actual framed evaluation sections form the actual
pullback of the chart tuple. -/
theorem framedSections_eCurve_eq_pullbackTuple :
    MukaiEvaluationCurveJets.framedSections K f E b u
        (eCurve K f E b d u h γ hfactor eChart) =
      MukaiEvaluationCurveJetChainRule.pullbackTuple K γ
        (MukaiConormalChartFrame.sectionTuple K h eChart) := by
  funext j
  exact framedSections_eCurve K f E b d u h γ hfactor eChart j

include d hfactor in
omit [CharZero K] in
/-- The original diagram and chart base triangle derive the actual
base triangle for the curve-to-chart map. -/
theorem gamma_overBase
    (hh : h ≫ LagrangianGrassmannian.projection K = MukaiConormalChartJets.chartProjection K) :
    γ ≫ MukaiConormalChartJets.chartProjection K = u ≫ f := by
  have hs := congrArg (fun t => t ≫ LagrangianGrassmannian.projection K) hfactor
  simpa only [Category.assoc, hh, d.over_base] using hs

/-- The actual evaluation sections, in the frame constructed from the
given chart frame, satisfy the native jet chain rule. -/
theorem curveJet_framedSections_eCurve
    (hh : h ≫ LagrangianGrassmannian.projection K = MukaiConormalChartJets.chartProjection K)
    (z : Spec (.of K) ⟶ Y) :
    MukaiEvaluationCurveJets.curveJet K (u ≫ f) z
        (MukaiEvaluationCurveJets.framedSections K f E b u
          (eCurve K f E b d u h γ hfactor eChart)) =
      (MukaiEvaluationCurveJetChainRule.jetTargetMap K (u ≫ f) γ
        (gamma_overBase K f E b d u h γ hfactor hh) z).comp
          (MukaiConormalChartJets.firstJetMap K (z ≫ γ)
            (MukaiConormalChartFrame.sectionTuple K h eChart)) := by
  rw [framedSections_eCurve_eq_pullbackTuple]
  exact MukaiEvaluationCurveJetChainRule.curveJet_pullbackTuple K (u ≫ f) γ
    (gamma_overBase K f E b d u h γ hfactor hh) z _

end M9Native.MukaiEvaluationCurveJetFrames

module

public import M9StacksIntegration.MukaiCurvePointLine
public import M9StacksIntegration.MukaiDualPullbackSections
public import M9StacksIntegration.MukaiConormalPositivePoint
public import M9StacksIntegration.MukaiEvaluationCurveJetFrames

/-! The actual inverse determinant point line contains the actual
positive primitive vector in the very same translated-origin frame.
The line frame and all section comparisons are constructed from the
original evaluation diagram and native pullback comparisons. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit

universe u

namespace M9Native.MukaiCurvePointLineValues

open MukaiCurvePointLine MukaiPrimitiveCanonicalEvaluation MukaiDualPullbackSections
open MukaiPointLine
open MukaiConormalPositivePoint MukaiConormalOriginFrame
open LagrangianTranslatedCharts LagrangianTranslatedDeterminantSections
open MukaiConormalChartJets MukaiCubicFreeSheaf LinearIncidenceTensorCoordinates
open LagrangianMatrixChart AlgebraicGeometry.Grassmannian
open SectionZeroIdealFactorization

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0)) (d : EvaluationDiagram K f E b)

abbrev pointDeterminantQuotient (p : Spec (.of K) ⟶ X) :=
  pulledQuotient p (determinantQuotient K f E b d)

def pointDeterminantFrame (p : Spec (.of K) ⟶ X)
    (g : Matrix.symplecticGroup (Fin 3) K)
    (hg : p ≫ d.map = zeroPoint K ≫ translatedBigCell K g) :
    (Scheme.Modules.pullback p).obj (Scheme.Modules.exteriorPower E (3 : ℤ)) ≅
      SheafOfModules.unit (Spec (.of K)).ringCatSheaf :=
  MukaiEvaluationCurveJetFrames.eCurve K f E b d p (translatedBigCell K g)
    (zeroPoint K) hg.symm (translatedDeterminantIso K g)

theorem pointDeterminantFrame_column (p : Spec (.of K) ⟶ X)
    (g : Matrix.symplecticGroup (Fin 3) K)
    (hg : p ≫ d.map = zeroPoint K ≫ translatedBigCell K g) (j : Fin 14) :
    unitCoordinate (Spec (.of K)) ((pointDeterminantFrame K f E b d p g hg).hom.app ⊤
      ((pointDeterminantQuotient K f E b d p).app ⊤
        (freeBasisSection (Spec (.of K)) 14 j))) =
      (Scheme.ΓSpecIso (.of K)).inv.hom
        ((LagrangianPluckerLinear.primitiveBasis14 K).repr
          (positivePoint K (zeroPoint K) g) j) := by
  change unitCoordinate (Spec (.of K)) ((pointDeterminantFrame K f E b d p g hg).hom.app ⊤
    (((Scheme.Modules.pullback p).map (determinantQuotient K f E b d)).app ⊤
      ((pullbackFreeIso p 14).inv.app ⊤ (freeBasisSection (Spec (.of K)) 14 j)))) = _
  rw [FiniteFreeBasisPullback.inverse_freeBasisSection_pullback,
    pullback_map_app_pullbackGlobalSections, determinantQuotient_column]
  change MukaiEvaluationCurveJets.framedSections K f E b p
    (pointDeterminantFrame K f E b d p g hg) j = _
  rw [pointDeterminantFrame,MukaiEvaluationCurveJetFrames.framedSections_eCurve]
  rw [← Module.Basis.equivFun_apply,positivePoint_coordinates]
  change (zeroPoint K).appTop (MukaiConormalChartCovariance.sectionTuple K g j) =
    (Scheme.ΓSpecIso (.of K)).inv.hom
      ((Scheme.ΓSpecIso (.of K)).hom
        ((zeroPoint K).appTop (MukaiConormalChartCovariance.sectionTuple K g j)))
  exact ((Scheme.ΓSpecIso (.of K)).hom_inv_id_apply _).symm

variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- The actual pulled original curve point line, not an abstract line
with the same rank, contains the exact original positive point section. -/
theorem positivePoint_preimage (p : Spec (.of K) ⟶ X)
    (g : Matrix.symplecticGroup (Fin 3) K)
    (hg : p ≫ d.map = zeroPoint K ≫ translatedBigCell K g) :
    ∃ a : Γ((Scheme.Modules.pullback p).obj
      (dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ))), ⊤),
      (pullbackFreeIso p 14).hom.app ⊤
        (((Scheme.Modules.pullback p).map (curvePointLine K f E b d)).app ⊤ a) =
      pointSection K (𝟙 (Spec (.of K))) (positivePoint K (zeroPoint K) g) := by
  have hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Modules.exteriorPower E (3 : ℤ)) :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3).isFiniteLocallyFree
  let eD := Stacks.FundamentalGroup.pullbackDualSheafIso p
    (Scheme.Modules.exteriorPower E (3 : ℤ)) hQ
  obtain ⟨a,ha⟩ := pointSection_preimage K (pointDeterminantQuotient K f E b d p)
    (pointDeterminantFrame K f E b d p g hg) (positivePoint K (zeroPoint K) g)
    (pointDeterminantFrame_column K f E b d p g hg)
  refine ⟨eD.inv.app ⊤ a,?_⟩
  have hs := pointLineMap_pullback p (determinantQuotient K f E b d) hQ
  change ((Scheme.Modules.pullback p).map (pointLineMap (determinantQuotient K f E b d)) ≫
    (pullbackFreeIso p 14).hom).app ⊤ (eD.inv.app ⊤ a) = _
  rw [hs]
  change (pointLineMap (pointDeterminantQuotient K f E b d p)).app ⊤
    (eD.hom.app ⊤ (eD.inv.app ⊤ a)) = _
  have hc := congrArg (fun t => t.app ⊤ a) eD.inv_hom_id
  change eD.hom.app ⊤ (eD.inv.app ⊤ a) = a at hc
  rw [hc]
  exact ha

end M9Native.MukaiCurvePointLineValues

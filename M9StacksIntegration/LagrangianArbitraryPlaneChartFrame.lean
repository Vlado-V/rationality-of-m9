module

public import M9StacksIntegration.LagrangianAffinePlaneSection
public import M9StacksIntegration.FreeTwoProjectiveChartCoordinates
public import M9StacksIntegration.RightLineTensorFrame
public import M9StacksIntegration.TwoChartTensorEquation
public import M9StacksIntegration.TensorPairingTopComparison
public import M9StacksIntegration.PullbackCompositeVectorFrame
public import M9StacksIntegration.SplitTwoFrameCoordinates

/-! Actual tautological-coordinate normalization of the original
arbitrary-plane incidence tensor on both genuine P1 charts. The source
bundle and section retain their original Q-first tensor order. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option Elab.async false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module Opposite
open scoped BigOperators
universe u

namespace M9Native.LagrangianArbitraryPlaneChartFrame

open LagrangianGrassmannian LagrangianPluckerQuotient
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable (K : Type u) [Field K]

abbrev chartSpace : Scheme.{u} := LagrangianAffinePlaneSection.chartSpace K

def chart (i : Fin 2) : chartSpace K ⟶ LagrangianArbitraryPlaneIncidence.ambient K :=
  FreeTwoProjectiveCharts.chart (space K) i

instance chart_isOpenImmersion (i : Fin 2) : IsOpenImmersion (chart K i) := by
  dsimp [chart]
  infer_instance

@[reassoc] theorem chart_projection (i : Fin 2) :
    chart K i ≫ LagrangianArbitraryPlaneIncidence.toLG K = LagrangianAffinePlaneSection.toLG K :=
  FreeTwoProjectiveCharts.chart_projection (space K) i

/-- The original quotient pullback is retained through the actual
chart's projection triangle. -/
def quotientIso (i : Fin 2) :
    (Scheme.Modules.pullback (chart K i)).obj (LagrangianArbitraryPlaneIncidence.quotientBundle K) ≅
      LagrangianAffinePlaneSection.quotientBundle K :=
  (Scheme.Modules.pullbackComp (chart K i) (LagrangianArbitraryPlaneIncidence.toLG K)).app
    (quotientOnLG K).target ≪≫
    (Scheme.Modules.pullbackCongr (chart_projection K i)).app (quotientOnLG K).target

theorem quotientIso_apply (i : Fin 2) (w : Fin 2 → LagrangianRing.V K) (j : Fin 2) :
    (quotientIso K i).hom.app ⊤
      (pullbackGlobalSections (chart K i) (LagrangianArbitraryPlaneIncidence.quotientBundle K)
        (LagrangianArbitraryPlaneIncidence.quotientSection K w j)) =
      pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w j) :=
  PullbackCompositeVectorFrame.iso_section (chart K i)
    (LagrangianArbitraryPlaneIncidence.toLG K) (LagrangianAffinePlaneSection.toLG K)
    (chart_projection K i) (quotientOnLG K).target
    (LagrangianArbitraryPlaneIncidence.originalSection K w j)

/-- The actual tautological frame with the same literal chart and
bundle type as the original incidence. -/
def lineFrame (i : Fin 2) :
    (Scheme.Modules.pullback (chart K i)).obj (LagrangianArbitraryPlaneIncidence.lineBundle K) ≅
      (SheafOfModules.unit (chartSpace K).ringCatSheaf : (chartSpace K).Modules) :=
  FreeTwoProjectiveCharts.chartFrame (space K) i

/-- The original native classifier triangle is retained on the actual
public chart and actual structural maps, before evaluating sections. -/
private theorem lineFrame_triangle_actual (i : Fin 2) :
    (Scheme.Modules.pullbackCongr (chart_projection K i)).inv.app
        (LagrangianArbitraryPlaneIncidence.planeSource K) ≫
      Stacks.Modules.quotientMapAlong (LagrangianArbitraryPlaneIncidence.toLG K)
        (Stacks.Chow.bundleTautological (LagrangianArbitraryPlaneIncidence.planeSource K))
        (chart K i) ≫ (lineFrame K i).hom =
      SplitTwoFrameCoordinates.quotientMap (LagrangianAffinePlaneSection.toLG K)
        (LagrangianAffinePlaneSection.parameter K) i := by
  calc
    _ = FreeTwoProjectiveCharts.chartQuotientMap (space K) i := by
      rw [← Category.assoc]
      change FreeTwoProjectiveCharts.pulledTautological (space K) i ≫
        (FreeTwoProjectiveCharts.chartFrame (space K) i).hom = _
      exact FreeTwoProjectiveCharts.chartFrame_triangle (space K) i
    _ = SplitTwoFrameCoordinates.quotientMap (LagrangianAffinePlaneSection.toLG K)
        (LagrangianAffinePlaneSection.parameter K) i := by
      unfold FreeTwoProjectiveCharts.chartQuotientMap SplitTwoFrameCoordinates.quotientMap
      congr 1
      exact FreeTwoProjectiveChartCoordinates.coordinateMap_eq (space K)

theorem lineFrame_coordinate (i j : Fin 2) :
    (lineFrame K i).hom.app ⊤
      (pullbackGlobalSections (chart K i) (LagrangianArbitraryPlaneIncidence.lineBundle K)
        (LagrangianArbitraryPlaneIncidence.lineCoordinate K j)) =
      if j=i then (1 : Γ(chartSpace K,⊤)) else LagrangianAffinePlaneSection.parameter K :=
  SplitTwoFrameCoordinates.frame_coordinate
    (LagrangianAffinePlaneSection.toLG K) (LagrangianAffinePlaneSection.parameter K)
    (LagrangianArbitraryPlaneIncidence.toLG K) (LagrangianArbitraryPlaneIncidence.lineBundle K)
    (Stacks.Chow.bundleTautological (LagrangianArbitraryPlaneIncidence.planeSource K))
    (chart K i) (chart_projection K i) i (lineFrame K i) (lineFrame_triangle_actual K i) j

/-- A native tensor comparison and the actual tautological line frame
remove only the O1 factor; Q remains the original untrivialized quotient. -/
def tensorFrame (i : Fin 2) :
    (Scheme.Modules.pullback (chart K i)).obj (LagrangianArbitraryPlaneIncidence.equationBundle K) ≅
      LagrangianAffinePlaneSection.quotientBundle K :=
  RightLineTensorFrame.frame (chart K i)
    (LagrangianArbitraryPlaneIncidence.quotientBundle K)
    (LagrangianArbitraryPlaneIncidence.lineBundle K)
    (LagrangianAffinePlaneSection.quotientBundle K)
    (quotientIso K i) (lineFrame K i)

theorem tensorSection_eq_tensorTop
    (s : Γ(LagrangianArbitraryPlaneIncidence.quotientBundle K,⊤))
    (t : Γ(LagrangianArbitraryPlaneIncidence.lineBundle K,⊤)) :
    LagrangianArbitraryPlaneIncidence.tensorSection K s t =
      LinearIncidenceTensorCoordinates.tensorTop (LagrangianArbitraryPlaneIncidence.ambient K)
        (LagrangianArbitraryPlaneIncidence.quotientBundle K)
        (LagrangianArbitraryPlaneIncidence.lineBundle K) s t :=
  TensorPairingTopComparison.pairing_eq_tensorTop (LagrangianArbitraryPlaneIncidence.ambient K)
    (LagrangianArbitraryPlaneIncidence.quotientBundle K)
    (LagrangianArbitraryPlaneIncidence.lineBundle K) s t

theorem tensorFrame_apply (i : Fin 2) (w : Fin 2 → LagrangianRing.V K) (j : Fin 2) :
    (tensorFrame K i).hom.app ⊤
      (pullbackGlobalSections (chart K i) (LagrangianArbitraryPlaneIncidence.equationBundle K)
        (LagrangianArbitraryPlaneIncidence.tensorSection K
          (LagrangianArbitraryPlaneIncidence.quotientSection K w j)
          (LagrangianArbitraryPlaneIncidence.lineCoordinate K j))) =
      (if j=i then (1 : Γ(chartSpace K,⊤)) else LagrangianAffinePlaneSection.parameter K) •
        pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
          (LagrangianArbitraryPlaneIncidence.originalSection K w j) := by
  rw [tensorSection_eq_tensorTop]
  change (RightLineTensorFrame.frame (chart K i)
    (LagrangianArbitraryPlaneIncidence.quotientBundle K)
    (LagrangianArbitraryPlaneIncidence.lineBundle K)
    (LagrangianAffinePlaneSection.quotientBundle K)
    (quotientIso K i) (lineFrame K i)).hom.app ⊤ _ = _
  rw [RightLineTensorFrame.frame_apply,quotientIso_apply]
  congr 1
  exact lineFrame_coordinate K i j

/-- The second genuine chart reverses the original plane basis. -/
def orderedFrame (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) : Fin 2 → LagrangianRing.V K :=
  if i=0 then w else w ∘ Equiv.swap (0 : Fin 2) 1

theorem orderedFrame_independent (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) (i : Fin 2) : LinearIndependent K (orderedFrame K w i) := by
  unfold orderedFrame
  split_ifs
  · exact hw
  · exact hw.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1).injective

/-- The original sum of two tensor sections becomes the literal
Q(w_i)+tQ(w_other) equation on the actual native chart. -/
theorem tensorFrame_equationSection (i : Fin 2) (w : Fin 2 → LagrangianRing.V K) :
    (tensorFrame K i).hom.app ⊤
      (pullbackGlobalSections (chart K i) (LagrangianArbitraryPlaneIncidence.equationBundle K)
        (LagrangianArbitraryPlaneIncidence.equationSection K w)) =
      LagrangianAffinePlaneSection.lineSection K (orderedFrame K w i) := by
  simp only [LagrangianArbitraryPlaneIncidence.equationSection,map_sum,tensorFrame_apply]
  fin_cases i
  · change (∑ j : Fin 2, (if j=0 then (1 : Γ(chartSpace K,⊤)) else
        LagrangianAffinePlaneSection.parameter K) •
      pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w j)) =
      pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w 0) +
      LagrangianAffinePlaneSection.parameter K •
        pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
          (LagrangianArbitraryPlaneIncidence.originalSection K w 1)
    simp only [Fin.sum_univ_two,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false,one_smul]
  · change (∑ j : Fin 2, (if j=1 then (1 : Γ(chartSpace K,⊤)) else
        LagrangianAffinePlaneSection.parameter K) •
      pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w j)) =
      pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w 1) +
      LagrangianAffinePlaneSection.parameter K •
        pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K) (quotientOnLG K).target
          (LagrangianArbitraryPlaneIncidence.originalSection K w 0)
    simp only [Fin.sum_univ_two,show (0 : Fin 2) ≠ 1 by decide,ite_false,ite_true,one_smul]
    exact add_comm _ _

end M9Native.LagrangianArbitraryPlaneChartFrame

module

public import M9StacksIntegration.CurveBasePoint
public import M9StacksIntegration.DirectC9KernelNet
public import M9StacksIntegration.DirectC9SchurNonzero
public import M9StacksIntegration.GradedCapTopTraceNonvanishing
public import M9StacksIntegration.ChowFlagThreeGysin
public import M9StacksIntegration.ChowFlagThreeInputNormalization
public import M9StacksIntegration.ChowFlagThreeOriginalInputNormalization

/-! An actual degree-eight net on every original proper smooth
genus-nine curve. The actual flag incidence class, its three geometric
pushforwards, and the actual fundamental-class trace are used together. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower
open Stacks.Chow Stacks.Chow.GenuineChern
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u
namespace M9Native.DirectC9DegreeEightNet

open GradedCapVirtualSchur CurveTopChowClass GradedCapTopTrace

attribute [local irreducible] GradedCapTopTrace.topTrace

theorem nonempty_degree_eight_net
    (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
    [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]
    (hg : genus C.hom = 9) :
    Nonempty (LinearSeries k C.hom
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.hom)).le 8 2) := by
  letI : SmoothOfRelativeDimension 1 C.hom :=
    DirectC9FibreGeometry.original_relativeDimension k C
  let c₀ := CurveBasePoint.point k C
  let E := DirectC9Bundles.E10 k C c₀
  let F := DirectC9Bundles.F10 k C c₀
  letI hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 10 :=
    DirectC9Bundles.E10_rank k C c₀ hg
  letI hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10 :=
    DirectC9Bundles.F10_rank k C c₀
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E := hE.isFiniteLocallyFree
  let D := dualSheaf E
  letI hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 10 :=
    isFiniteLocallyFreeOfRank_dualSheaf E 10 hE
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D := hD.isFiniteLocallyFree
  let A := fieldChowSituation k
  let q := (power C 9).hom
  let π := FlagThreeIncidence.projection E
  let qFlag := π ≫ q
  letI : LocallyOfFiniteType π := ChowFlagThreeStages.originalProjectionLFT D
  letI : IsProper π := FlagTowerProper.isProper_tower 3 D
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (FlagThreeIncidence.incidenceBundle E F) 30 :=
    FlagThreeIncidence.incidenceBundle_rank_thirty E F hF
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback π).obj F) 10 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback π F 10
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (FlagThreeIncidence.quotientBundle E) 3 :=
    FlagThreeIncidence.quotientBundle_rank E
  let T := Scheme.Modules.tensorObj (FlagThreeIncidence.quotientBundle E)
    ((Scheme.Modules.pullback π).obj F)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} T 30 :=
    FlagThreeTensorChern.tensor_rank _ _ 3 10
  let α : chowGroup A q 9 := identityChowClass A q 9
  let β : chowGroup A qFlag 30 :=
    ChowFlagThreeStages.normalClassOnOriginalFlag D A q 9 α
  let v : GradedCapFamily (chowGroup A q) :=
    schur333 (virtualFamily A q F E 10 10)
  by_contra hno
  have hzero : chernCap A 30 qFlag
      (FlagThreeIncidence.incidenceBundle E F) 30 (Fin.last 30) β = 0 :=
    DirectC9KernelNet.topCap_eq_zero_of_no_net k C c₀ hg hno 30 β
  have hTensorZero : chernCap A 30 qFlag T 30 (Fin.last 30) β = 0 :=
    (FlagThreeTensorChern.incidence_topCap_eq_tensor E F A qFlag 30 β).symm.trans hzero
  have hnormal :=
    ChowFlagThreeInputNormalization.tensor_on_normalClassOnOriginalFlag_heq D F A q 9 α
  have hInputZero : ChowFlagThreeInputs.normalTensorInputOnOriginalFlag D F A q 9 α = 0 := by
    apply eq_of_heq
    exact hnormal.symm.trans (heq_of_eq hTensorZero)
  have hpush := ChowFlagThreeGysin.push_original_normalTensorInput_dual_eq_schur E F A q 9 α
  have hSchurZero : v 9 9 α = 0 := by
    rw [hInputZero, ChowFlagThreeGysin.pushOnOriginalFlag_zero] at hpush
    exact hpush.symm
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      generalize hv : v = w at hSchurZero
      have hTraceZeroW : topTrace k q 9 w = 0 := by
        change w (9 : ℤ) (9 : ℕ)
          (identityChowClass (fieldChowSituation k) q (9 : ℤ)) = 0 at hSchurZero
        exact GradedCapTopTraceNonvanishing.topTrace_eq_zero_of_fundamental_component_eq_zero
          k q 9 w hSchurZero
      have hTraceZero : topTrace k q 9 v = 0 :=
        (congrArg (topTrace k q 9) hv).trans hTraceZeroW
      have hTraceValue : topTrace k q 9 v = 15240960 := by
        exact DirectC9SchurNonzero.virtualSchur_topTrace k C c₀ hg
      have hbad : (15240960 : ℤ) = 0 := hTraceValue.symm.trans hTraceZero
      norm_num at hbad

end M9Native.DirectC9DegreeEightNet

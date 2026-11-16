module

public import M9StacksIntegration.NativeProjectiveChartComparison
public import M9StacksIntegration.ConicFrameFieldComparison
import all M9.Private.ProjectiveCharts

/-! Named-coordinate compatibility of the native projective matrix models. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace M9Native.ConicFrameChartActionComparison

open ConicFrameProjective ConicFrameGammaAction NativeProjectiveChartComparison
open M9.ProjectiveGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem legacy_chart_inverse (n : ℕ) (i : Fin (n+1)) :
    (PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm.toRingHom =
      chartHom ℂ n i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change PolynomialToProjectiveChart.polynomialToProjectiveChart n i (MvPolynomial.C c) = _
    rw [PolynomialToProjectiveChart.polynomialToProjectiveChart_C,chartHom_C,
      coeffToAway_eq_mk]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
    rw [PolynomialToProjectiveChart.projectiveChartConstants_val,
      HomogeneousLocalization.Away.val_mk]
    change algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
      (Localization.Away (MvPolynomial.X i)) (MvPolynomial.C c) =
      Localization.mk (MvPolynomial.C c) 1
    exact (Localization.mk_one_eq_algebraMap (MvPolynomial.C c)).symm
  · intro j
    rfl

theorem legacy_chart_ringEquiv (n : ℕ) (i : Fin (n+1)) :
    PolynomialToProjectiveChart.projectiveChartRingEquiv n i =
      (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv ℂ n i).symm := by
  apply DFunLike.ext
  intro a
  apply (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv ℂ n i).injective
  rw [RingEquiv.apply_symm_apply]
  change chartHom ℂ n i (PolynomialToProjectiveChart.projectiveChartRingEquiv n i a) = a
  rw [← legacy_chart_inverse]
  exact (PolynomialToProjectiveChart.projectiveChartRingEquiv n i).symm_apply_apply a

theorem nativeChart_to_polynomialChart :
    ConicFrameProjective.chart ℂ ≫ nativeSchemeIso.hom =
      polynomialChart ℂ (Fin 8) 8 0 (finSuccAboveEquiv 0) := by
  apply (cancel_mono nativeSchemeIso.inv).mp
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  change ConicFrameProjective.chart ℂ =
    polynomialChart ℂ (Fin 8) 8 0 (finSuccAboveEquiv 0) ≫ projCompare ℂ 8
  rw [ConicFrameProjective.chart,
    affineChart_comparison ℂ (ULift (Fin 8)) 8 0
      (Equiv.ulift.trans (finSuccAboveEquiv 0)),← Category.assoc]
  congr 1
  rw [polynomialChart,polynomialChart,← Category.assoc,← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (MvPolynomial.renameEquiv ℂ Equiv.ulift)
      ((chartRingEquiv ℂ (ULift (Fin 8)) 8 0
        (Equiv.ulift.trans (finSuccAboveEquiv 0))).symm a) =
    (chartRingEquiv ℂ (Fin 8) 8 0 (finSuccAboveEquiv 0)).symm a
  obtain ⟨p,rfl⟩ := (chartRingEquiv ℂ (Fin 8) 8 0 (finSuccAboveEquiv 0)).surjective a
  rw [RingEquiv.symm_apply_apply]
  have hh : chartRingEquiv ℂ (ULift (Fin 8)) 8 0
      (Equiv.ulift.trans (finSuccAboveEquiv 0))
        ((MvPolynomial.renameEquiv ℂ Equiv.ulift).symm p) =
      chartRingEquiv ℂ (Fin 8) 8 0 (finSuccAboveEquiv 0) p := by
    change chartHom ℂ 8 0 (MvPolynomial.rename (Equiv.ulift.trans (finSuccAboveEquiv 0))
        (MvPolynomial.rename Equiv.ulift.symm p)) =
      chartHom ℂ 8 0 (MvPolynomial.rename (finSuccAboveEquiv 0) p)
    rw [MvPolynomial.rename_rename]
    rfl
  rw [← hh,RingEquiv.symm_apply_apply]
  exact AlgEquiv.apply_symm_apply _ p

theorem polynomialChart_eq_legacy :
    polynomialChart ℂ (Fin 8) 8 0 (finSuccAboveEquiv 0) =
      Spec.map (CommRingCat.ofHom (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0).toRingHom) ≫
        M9.ProjectiveFunctionField.chartMap 8 0 := by
  rw [M9.ProjectiveFunctionField.chartMap,ProjectiveChart.projectiveAffineChartMap,
    ProjectiveChart.projectiveCoordinateIsoSpec_inv_ι,← Category.assoc,← Spec.map_comp]
  unfold polynomialChart
  congr 2
  apply CommRingCat.hom_ext
  change (chartRingEquiv ℂ (Fin 8) 8 0 (finSuccAboveEquiv 0)).symm.toRingHom = _
  rw [chartRingEquiv]
  have h := legacy_chart_ringEquiv 8 0
  change _ = ((M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0).toRingHom).comp
    (PolynomialToProjectiveChart.projectiveChartRingEquiv 8 0).toRingHom
  rw [h]
  rfl

theorem nativeChart_eq_legacy :
    ConicFrameProjective.chart ℂ ≫ nativeSchemeIso.hom =
      Spec.map (CommRingCat.ofHom (M9.ProjectiveFunctionField.chartCoordinatesEquiv 8 0).toRingHom) ≫
        M9.ProjectiveFunctionField.chartMap 8 0 :=
  nativeChart_to_polynomialChart.trans polynomialChart_eq_legacy

end M9Native.ConicFrameChartActionComparison

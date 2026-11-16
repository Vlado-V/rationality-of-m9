module

public import M9StacksIntegration.DegreeFivePencilNormalization
public import M9StacksIntegration.LagrangianIncidenceBetaEight
public import M9StacksIntegration.LagrangianNoFreeFiveLine
public import M9StacksIntegration.LagrangianNoTrigonal
public import M9StacksIntegration.LagrangianNoTetragonal
public import M9StacksIntegration.LagrangianTransverseGenusNine
public import M9StacksIntegration.MukaiCurveIsoLinearSeries

/-! Universal nonpentagonality of the actual original smooth integral
five-row LG section. Actual genus, no-three, no-four, complete degree-five
pencil normalization, actual rank-two subsystem and actual determinant
degree eight are all derived inside the proof. The final headers supply
none of those conclusions or subsystem choices. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.LagrangianNonpentagonal

open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles LagrangianBetaRankDrop
open LagrangianFreeFiveResidualSections

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

section Model

variable [IsIntegral (model K M hM)]
    [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- The original smooth integral model has no degree-five pencil,
including pencils with base points. No numerical or no-pencil datum is
assumed beyond the actual original curve geometry. -/
theorem model_no_g1_five :
    ¬ Nonempty (LinearSeries K (modelProjection K M hM)
      (dimension_le_one K M hM) 5 1) := by
  letI : IsCurve K (modelProjection K M hM) := model_isCurve K M hM
  letI : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  letI : IsIntegral (LagrangianTransverseRestriction.curve K M) :=
    LagrangianModelRestriction.ordered_integral K M hM
  letI : SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M) :=
    LagrangianModelRestriction.ordered_smooth K M hM
  let hordered : topologicalKrullDim (LagrangianTransverseRestriction.curve K M) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one
      (k := K) (f := LagrangianTransverseRestriction.curveProjection K M)).le
  have hno3ordered := LagrangianNoTrigonal.no_g1_three_at_dimension K M hM hordered
  have hno4ordered := LagrangianNoTetragonal.no_g1_four_at_dimension K M hM hordered
  have hno3 : ¬ Nonempty (LinearSeries K (modelProjection K M hM)
      (dimension_le_one K M hM) 3 1) :=
    (not_congr (MukaiCurveIsoLinearSeries.nonempty_linearSeries_iff K
      (LagrangianTransverseRestriction.curveProjection K M) (modelProjection K M hM)
      (cutIsoModel K M hM) (cutIsoModel_hom_base K M hM)
      hordered (dimension_le_one K M hM) 3 1)).mp hno3ordered
  have hno4 : ¬ Nonempty (LinearSeries K (modelProjection K M hM)
      (dimension_le_one K M hM) 4 1) :=
    (not_congr (MukaiCurveIsoLinearSeries.nonempty_linearSeries_iff K
      (LagrangianTransverseRestriction.curveProjection K M) (modelProjection K M hM)
      (cutIsoModel K M hM) (cutIsoModel_hom_base K M hM)
      hordered (dimension_le_one K M hM) 4 1)).mp hno4ordered
  have hg : genus (modelProjection K M hM) = 9 :=
    (LagrangianBetaCurveDegree.model_genus_eq_ordered K M hM).trans
      (LagrangianTransverseGenusNine.genus_eq_nine K M hM)
  rintro ⟨A⟩
  let := A.isInvertible
  obtain ⟨t, h2, ht⟩ := DegreeFivePencilNormalization.exists_generating_pair
    (modelProjection K M hM) (dimension_le_one K M hM) hno4 A
  obtain ⟨s, hs, _hsections, hdet, hr⟩ :=
    MukaiDeterminantZeroSubsystem.exists_rank_two_subsystem K M hM
  obtain ⟨e, he⟩ :=
    LagrangianRankTwoSubsystemExistence.exists_nonzero_pair_section K M hM s hr
  obtain ⟨B, _hBM, hfirst, _hnonzero⟩ :=
    LagrangianTripleFirstEquation.exists_first_equation K M hM s hs hdet
  have hbeta := betaSection_ne_zero K M hM s hr e he
  have hlength := LagrangianIncidenceBetaEight.nativeBetaZeroLength_eq_eight
    K M hM s hr e (hs.comp e e.injective) hbeta B hfirst
  have hβ : letI := beta_isInvertible K M hM s hr
      invertibleCurveDegree K (modelProjection K M hM) (dimension_le_one K M hM)
        (beta K M hM s) = 8 := by
    letI := beta_isInvertible K M hM s hr
    have hd := LagrangianBetaCurveDegree.betaDegree_eq_nativeBetaZeroLength
      K M hM s hr e hbeta
    rw [hlength] at hd
    simpa only [LagrangianBetaCurveDegree.betaDegree, Nat.cast_ofNat] using hd
  exact LagrangianNoFreeFiveLine.false_of_free_five_line
    K M hM s hs hr hg hno3 A.L hβ A.degree_eq h2 t ht

end Model

section Ordered

variable [IsIntegral (LagrangianTransverseRestriction.curve K M)]
    [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)]

include hM

/-- The same conclusion for the literal original ordered five-row cut,
with the original field and original linear-series type retained. -/
theorem no_g1_five_at_dimension
    (hdim : topologicalKrullDim (LagrangianTransverseRestriction.curve K M) ≤ 1) :
    ¬ Nonempty (LinearSeries K (LagrangianTransverseRestriction.curveProjection K M) hdim 5 1) := by
  letI : IsIntegral (model K M hM) := IsIntegral.of_isIso (cutIsoModel K M hM).hom
  have hbase : (cutIsoModel K M hM).inv ≫
      LagrangianTransverseRestriction.curveProjection K M = modelProjection K M hM :=
    (cutIsoModel K M hM).inv_comp_eq.mpr (cutIsoModel_hom_base K M hM).symm
  letI : SmoothOfRelativeDimension 1 (modelProjection K M hM) := by
    have h : SmoothOfRelativeDimension (0 + 1)
        ((cutIsoModel K M hM).inv ≫ LagrangianTransverseRestriction.curveProjection K M) :=
      inferInstance
    simpa only [zero_add, hbase] using h
  exact (not_congr (MukaiCurveIsoLinearSeries.nonempty_linearSeries_iff K
    (LagrangianTransverseRestriction.curveProjection K M) (modelProjection K M hM)
    (cutIsoModel K M hM) (cutIsoModel_hom_base K M hM)
    hdim (dimension_le_one K M hM) 5 1)).mpr (model_no_g1_five K M hM)

end Ordered

end M9Native.LagrangianNonpentagonal

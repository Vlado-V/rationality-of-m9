module

public import M9StacksIntegration.LagrangianArbitraryPlaneChartFrame
public import M9StacksIntegration.FreeTwoProjectiveChartCover
public import M9StacksIntegration.ExteriorTwoSectionRelation
public import M9StacksIntegration.SectionZeroOpenCover
public import M9StacksIntegration.IteratedLineSectionCuts
public import M9StacksIntegration.LagrangianPairDeterminantContainment

/-!
# The actual arbitrary-plane incidence maps to its full pair rank drop

The two genuine P1 charts carry the original Q-first tensor equation to
the actual relation Q(w0)+t Q(w1), or its reversed version. These true
relations annihilate the actual wedge over arbitrary rings. Descent on
the actual open cover therefore gives full section vanishing, and the
actual native zero-scheme universal property constructs the map.
This is a morphism, with its original LG projection; no global
incidence-to-rank-drop isomorphism is assumed or claimed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
universe u

namespace M9Native.LagrangianIncidenceRankDrop
open LagrangianGrassmannian LagrangianPluckerQuotient
variable (K : Type u) [Field K]


private theorem chart_wedge_zero {T : Scheme.{u}} (i : Fin 2)
    (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K)
    (q : T ⟶ LagrangianArbitraryPlaneChartFrame.chartSpace K)
    (h : pullbackGlobalSections q (LagrangianAffinePlaneSection.quotientBundle K)
      (LagrangianAffinePlaneSection.lineSection K
        (LagrangianArbitraryPlaneChartFrame.orderedFrame K w i)) = 0) :
    pullbackGlobalSections (q ≫ LagrangianAffinePlaneSection.toLG K)
      (LagrangianArbitraryPlaneIncidence.wedgeBundle K)
      (LagrangianArbitraryPlaneIncidence.wedgeEquation K w) = 0 := by
  let E := LagrangianAffinePlaneSection.quotientBundle K
  let s := pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K)
    (quotientOnLG K).target (LagrangianArbitraryPlaneIncidence.originalSection K w 0)
  let t := pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K)
    (quotientOnLG K).target (LagrangianArbitraryPlaneIncidence.originalSection K w 1)
  have hw : wedgeSection T ((Scheme.Modules.pullback q).obj E)
      (pullbackGlobalSections q E s) (pullbackGlobalSections q E t) = 0 := by
    fin_cases i
    · apply ExteriorTwoSectionRelation.wedge_zero_of_left_relation _
        (q.appTop.hom (LagrangianAffinePlaneSection.parameter K))
      change pullbackGlobalSections q E (s + LagrangianAffinePlaneSection.parameter K • t) = 0 at h
      simpa only [map_add, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul] using h
    · apply ExteriorTwoSectionRelation.wedge_zero_of_right_relation _
        (q.appTop.hom (LagrangianAffinePlaneSection.parameter K))
      change pullbackGlobalSections q E (t + LagrangianAffinePlaneSection.parameter K • s) = 0 at h
      simpa only [map_add, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul] using h
  have hwq : pullbackGlobalSections q (Scheme.Modules.exteriorPower E (2 : ℤ))
      (wedgeSection _ E s t) = 0 := by
    apply (map_eq_zero_iff _ (SectionZeroSubbundle.appTop_injective_of_mono
      (LagrangianPullback.exteriorPullbackIso q E 2).hom)).mp
    rw [exteriorPullback_wedgeSection]
    exact hw
  have hwp : pullbackGlobalSections q
      ((Scheme.Modules.pullback (LagrangianAffinePlaneSection.toLG K)).obj
        (LagrangianArbitraryPlaneIncidence.wedgeBundle K))
      (pullbackGlobalSections (LagrangianAffinePlaneSection.toLG K)
        (LagrangianArbitraryPlaneIncidence.wedgeBundle K)
        (LagrangianArbitraryPlaneIncidence.wedgeEquation K w)) = 0 := by
    apply (LagrangianMatrixChart.pullbackSection_eq_zero_iff_of_iso q
      (LagrangianPullback.exteriorPullbackIso (LagrangianAffinePlaneSection.toLG K)
        (quotientOnLG K).target 2) _).mpr
    rw [LagrangianArbitraryPlaneIncidence.wedgeEquation, exteriorPullback_wedgeSection]
    exact hwq
  exact (IteratedLineSectionCuts.pullback_comp_zero_iff
    (LagrangianArbitraryPlaneIncidence.wedgeBundle K) q
    (LagrangianAffinePlaneSection.toLG K)
    (LagrangianArbitraryPlaneIncidence.wedgeEquation K w)).mpr hwp

/-- The FULL original wedge vanishes on the FULL original incidence,
proved on its genuine two-chart open cover, including all nilpotents. -/

theorem incidence_wedge_zero (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) :
    pullbackGlobalSections (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
      (LagrangianArbitraryPlaneIncidence.wedgeBundle K)
      (LagrangianArbitraryPlaneIncidence.wedgeEquation K w) = 0 := by
  have hzero : pullbackGlobalSections
      (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)
      (LagrangianArbitraryPlaneIncidence.equationBundle K)
      (LagrangianArbitraryPlaneIncidence.equationSection K w) = 0 :=
    SectionZeroIdealFactorization.pullbackGlobalSections_subschemeι_eq_zero
      (LagrangianArbitraryPlaneIncidence.equationBundle K) 3
      (LagrangianArbitraryPlaneIncidence.equationSection K w)
  let U0 := FreeTwoProjectiveChartCover.chartCover (space K)
  let U := U0.pullback₁ (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)).obj
        (LagrangianArbitraryPlaneIncidence.wedgeBundle K)) 3 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
      (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
      (LagrangianArbitraryPlaneIncidence.wedgeBundle K) 3
  apply SectionZeroOpenCover.section_eq_zero_of_pullbacks_eq_zero _ 3 _ U
  intro i
  let j : Fin 2 := i
  let q := U0.pullbackHom (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w) i
  have hm : q ≫ LagrangianArbitraryPlaneChartFrame.chart K j =
      U.f i ≫ LagrangianArbitraryPlaneIncidence.incidenceInclusion K w :=
    U0.pullbackHom_map (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w) i
  have heq : pullbackGlobalSections
      (q ≫ LagrangianArbitraryPlaneChartFrame.chart K j)
      (LagrangianArbitraryPlaneIncidence.equationBundle K)
      (LagrangianArbitraryPlaneIncidence.equationSection K w) = 0 := by
    rw [hm]
    apply (IteratedLineSectionCuts.pullback_comp_zero_iff
      (LagrangianArbitraryPlaneIncidence.equationBundle K) (U.f i)
      (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)
      (LagrangianArbitraryPlaneIncidence.equationSection K w)).mpr
    exact (congrArg
      (fun a => pullbackGlobalSections (U.f i)
        ((Scheme.Modules.pullback
          (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)).obj
          (LagrangianArbitraryPlaneIncidence.equationBundle K)) a) hzero).trans
      (map_zero _)
  have heq' := (IteratedLineSectionCuts.pullback_comp_zero_iff
    (LagrangianArbitraryPlaneIncidence.equationBundle K) q
    (LagrangianArbitraryPlaneChartFrame.chart K j)
    (LagrangianArbitraryPlaneIncidence.equationSection K w)).mp heq
  have hframe : pullbackGlobalSections q (LagrangianAffinePlaneSection.quotientBundle K)
      (LagrangianAffinePlaneSection.lineSection K
        (LagrangianArbitraryPlaneChartFrame.orderedFrame K w j)) = 0 := by
    rw [← LagrangianArbitraryPlaneChartFrame.tensorFrame_equationSection K j w,
      ← SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
      heq', map_zero]
  have hp : q ≫ LagrangianAffinePlaneSection.toLG K =
      U.f i ≫ LagrangianArbitraryPlaneIncidence.incidenceToLG K w := by
    calc
      q ≫ LagrangianAffinePlaneSection.toLG K =
          q ≫ (LagrangianArbitraryPlaneChartFrame.chart K j ≫
            LagrangianArbitraryPlaneIncidence.toLG K) :=
        congrArg (fun a => q ≫ a)
          (LagrangianArbitraryPlaneChartFrame.chart_projection K j).symm
      _ = (q ≫ LagrangianArbitraryPlaneChartFrame.chart K j) ≫
          LagrangianArbitraryPlaneIncidence.toLG K := (Category.assoc _ _ _).symm
      _ = (U.f i ≫ LagrangianArbitraryPlaneIncidence.incidenceInclusion K w) ≫
          LagrangianArbitraryPlaneIncidence.toLG K :=
        congrArg (fun a => a ≫ LagrangianArbitraryPlaneIncidence.toLG K) hm
      _ = U.f i ≫ LagrangianArbitraryPlaneIncidence.incidenceToLG K w :=
        Category.assoc _ _ _
  apply (IteratedLineSectionCuts.pullback_comp_zero_iff
    (LagrangianArbitraryPlaneIncidence.wedgeBundle K) (U.f i)
    (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
    (LagrangianArbitraryPlaneIncidence.wedgeEquation K w)).mp
  rw [← hp]
  exact chart_wedge_zero K j w q hframe

/-- The actual incidence therefore has an actual morphism to the FULL
pair rank-drop scheme. No isomorphism is asserted. -/

def incidenceToRankDrop (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) :
    LagrangianArbitraryPlaneIncidence.incidence K w ⟶
      LagrangianArbitraryPlaneIncidence.rankDrop K w :=
  Classical.choose ((LagrangianArbitraryPlaneIncidence.factors_rankDrop_iff_wedge_zero K w
    (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)).mpr (incidence_wedge_zero K w))


@[reassoc]
theorem incidenceToRankDrop_toLG (w : LagrangianArbitraryPlaneIncidence.PlaneFrame K) :
    incidenceToRankDrop K w ≫ LagrangianArbitraryPlaneIncidence.rankDropInclusion K w =
      LagrangianArbitraryPlaneIncidence.incidenceToLG K w :=
  Classical.choose_spec ((LagrangianArbitraryPlaneIncidence.factors_rankDrop_iff_wedge_zero K w
    (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)).mpr (incidence_wedge_zero K w))

variable [CharZero K]

/-- The original triple hyperplane vanishes on the FULL incidence, so
it can be removed after an actual invertible change of the five rows. -/

theorem incidence_triple_hyperplane_zero (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    pullbackGlobalSections (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e))
      (determinantLine K) (LagrangianHyperplaneCoordinates.determinantSection K
        (PrimitiveDecomposableNonzero.coefficients K s)) = 0 :=
  LagrangianPairDeterminantContainment.hyperplane_zero_of_pair_zero K _ s e
    (incidence_wedge_zero K (s ∘ e))


end M9Native.LagrangianIncidenceRankDrop

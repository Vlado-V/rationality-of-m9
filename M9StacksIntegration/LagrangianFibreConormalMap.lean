module

public import M9StacksIntegration.VanishingSectionConormalMap
public import M9StacksIntegration.LagrangianFibreFiveSection
public import M9StacksIntegration.NativeVectorSectionZeroPullback

/-!
# The original five equations induce the actual curve conormal map

An actual factorization into the original incidence fibre forces the
actual five-section to vanish. Its original dual evaluation therefore
induces the genuine native conormal map. The source and target ranks
come from the literal equation bundle and the actual smooth source
curve; no smoothness of the entire incidence fibre is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u

namespace M9Native.LagrangianFibreConormalMap

open LagrangianGrassmannian LagrangianFiveSectionModel

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  (i : X ⟶ space K)
  (q : X ⟶ LagrangianFibreFactorization.fibre K
    (LagrangianMatrixPointRows.matrixPoint K M hM))
  (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
    (LagrangianMatrixPointRows.matrixPoint K M hM) = i)

include q hq in
/-- An original incidence-fibre factorization is a factorization through
the full native zero scheme of the actual original five-section. -/
theorem factorsThrough_zeroScheme :
    ∃ g : X ⟶ LagrangianFiveSectionModel.curve K
        (LagrangianFibreFiveSection.fiveSection K M hM),
      g ≫ LagrangianFiveSectionModel.inclusion K
        (LagrangianFibreFiveSection.fiveSection K M hM) = i := by
  let e := LagrangianFibreFiveSection.fiveSectionIsoFibre K M hM
  have he : e.inv ≫ LagrangianFiveSectionModel.inclusion K
      (LagrangianFibreFiveSection.fiveSection K M hM) =
        LagrangianFibreFactorization.fibreToLG K
          (LagrangianMatrixPointRows.matrixPoint K M hM) := by
    apply (cancel_epi e.hom).mp
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using
      (LagrangianFibreFiveSection.fiveSectionIsoFibre_hom_toLG K M hM).symm
  exact ⟨q ≫ e.inv, by simpa only [Category.assoc, he] using hq⟩

include q hq in
/-- The actual vector section vanishes in the actual pullback sheaf,
including on nonreduced test schemes. -/
theorem pullback_fiveSection_eq_zero :
    pullbackGlobalSections i (LagrangianFiveSectionModel.equationBundle K)
      (LagrangianFibreFiveSection.fiveSection K M hM) = 0 := by
  apply (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (LagrangianFiveSectionModel.equationBundle K) 5 (LagrangianFibreFiveSection.fiveSection K M hM) i).mpr
  rw [← NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal
    (LagrangianFiveSectionModel.equationBundle K) (LagrangianFibreFiveSection.fiveSection K M hM)]
  exact factorsThrough_zeroScheme K M hM i q hq

variable [IsClosedImmersion i]

/-- The actual original equation dual, on the original source curve. -/
abbrev source := (Scheme.Modules.pullback i).obj (dualSheaf (LagrangianFiveSectionModel.equationBundle K))

/-- The actual five-row map into the literal first term of the native
curve-in-LG conormal complex. -/
def sequenceMap : source K i ⟶ (LagrangianCurveConormal.sequence K i).X₁ :=
  VanishingSectionConormalMap.sequenceMap i (LagrangianFiveSectionModel.equationBundle K)
    (LagrangianFibreFiveSection.fiveSection K M hM)
    (pullback_fiveSection_eq_zero K M hM i q hq) (projection K)

omit [IsClosedImmersion i] in
/-- The source has rank five from the actual line-first equation bundle. -/
theorem source_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (source K i) 5 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (dualSheaf (LagrangianFiveSectionModel.equationBundle K)) 5 :=
    isFiniteLocallyFreeOfRank_dualSheaf (LagrangianFiveSectionModel.equationBundle K) 5 (LagrangianFiveSectionModel.equationBundle_rank K)
  exact isFiniteLocallyFreeOfRank_pullback i (dualSheaf (LagrangianFiveSectionModel.equationBundle K)) 5

/-- Actual smoothness of the original source curve derives the target
rank; smoothness of its entire incidence fibre is not assumed. -/
theorem target_rank [SmoothOfRelativeDimension 1 (i ≫ projection K)] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (LagrangianCurveConormal.sequence K i).X₁ 5 :=
  LagrangianCurveConormal.sequence_rank K i

/-- The row-to-conormal map retains the genuine positive native
equation differential on every local equation functional. -/
theorem sequenceMap_firstArrow_unit_apply (U : (space K).Opens)
    (τ : Γ(dualSheaf (LagrangianFiveSectionModel.equationBundle K), U)) :
    (sequenceMap K M hM i q hq ≫ (LagrangianCurveConormal.sequence K i).f).app (i ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (dualSheaf (LagrangianFiveSectionModel.equationBundle K))).app U τ) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (Scheme.Hom.relativeDifferentials (projection K))).app U
        ((Scheme.Hom.universalRelativeDerivation (projection K)).d
          (evalAt (LagrangianFiveSectionModel.equationBundle K) τ ((LagrangianFiveSectionModel.equationBundle K).presheaf.map (homOfLE le_top).op
            (LagrangianFibreFiveSection.fiveSection K M hM)))) :=
  VanishingSectionConormalMap.sequenceMap_firstArrow_unit_apply i (LagrangianFiveSectionModel.equationBundle K)
    (LagrangianFibreFiveSection.fiveSection K M hM)
    (pullback_fiveSection_eq_zero K M hM i q hq) (projection K) U τ

end M9Native.LagrangianFibreConormalMap

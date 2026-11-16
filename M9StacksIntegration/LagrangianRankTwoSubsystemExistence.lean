module

public import M9StacksIntegration.LagrangianRankTwoSubsystemBundles
public import M9StacksIntegration.RankTwoSubsystemWedge

/-!
# Actual original rank-two subsystem bundles and a nonzero pair section

This assembles the genuine subsystem-existence theorem with the actual
kernel/image/cokernel construction. The three image sections lift the
literal original three sections. A pair of those very sections gives a
nonzero global section of the genuine beta determinant. The actual
quotient sequence gives beta tensor alpha isomorphic to the canonical
line. All objects, ranks, exact sequences, pair and nonvanishing are
constructed; neither a residual degree nor Schubert incidence is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TopologicalSpace
open M9Native.MukaiBundleDeterminant

namespace M9Native.LagrangianRankTwoSubsystemExistence
open LagrangianRankTwoSubsystemBundles LagrangianOrderedFibre LagrangianUniversalSections
universe u
variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

abbrev imageSections (s : Fin 3 → (Fin 6 → K)) :=
  RankTwoSubsystemWedge.imageSections K (modelProjection K M hM) (originalMap K M hM s)

omit [CharZero K] in
/-- Every actual image section maps to the corresponding ORIGINAL
H0 section under the literal image inclusion. -/
theorem imageSections_maps_to_original (s : Fin 3 → (Fin 6 → K)) (i : Fin 3) :
    cohomologyOverFieldMap K (modelProjection K M hM)
      (image.ι (originalMap K M hM s)) 0 (imageSections K M hM s i) =
        sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i) :=
  RankTwoSubsystemWedge.imageSections_maps_to_original K (modelProjection K M hM)
    (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i)) i

omit [CharZero K] in
theorem imageSections_independent (s : Fin 3 → (Fin 6 → K))
    (hs : LinearIndependent K
      (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i))) :
    LinearIndependent K (imageSections K M hM s) := by
  apply LinearIndependent.of_comp
    (cohomologyOverFieldMap K (modelProjection K M hM) (image.ι (originalMap K M hM s)) 0).hom
  convert hs using 1
  funext i
  exact imageSections_maps_to_original K M hM s i

abbrev pairExteriorSection (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :=
  RankTwoSubsystemWedge.pairExteriorSection K (modelProjection K M hM)
    (originalMap K M hM s) e

omit [CharZero K] in
/-- The actual image-pair wedge maps to the actual exterior wedge of
the SAME two original H0 sections in Q. -/
theorem pairExteriorSection_maps_to_original (s : Fin 3 → (Fin 6 → K))
    (e : Fin 2 ↪ Fin 3) :
    cohomologyOverFieldMap K (modelProjection K M hM)
      (Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ)) 0
      (pairExteriorSection K M hM s e) =
    ExteriorEvaluation.lambda K (modelProjection K M hM) (bundle K (modelInclusion K M hM)) 2
      (exteriorPower.ιMulti K 2
        (fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s (e i)))) := by
  have h := LinearMap.congr_fun (ExteriorEvaluation.lambda_naturality K (modelProjection K M hM)
    (image.ι (originalMap K M hM s)) 2)
    (exteriorPower.ιMulti K 2 (imageSections K M hM s ∘ e))
  simp only [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti] at h
  have hv : (cohomologyOverFieldMap K (modelProjection K M hM)
      (image.ι (originalMap K M hM s)) 0).hom ∘ imageSections K M hM s ∘ e =
      fun i => sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s (e i)) := by
    funext i
    exact imageSections_maps_to_original K M hM s (e i)
  rw [hv] at h
  exact h

section IntegralSmooth
variable [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

def betaExteriorIso (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    beta K M hM s ≅ Scheme.Modules.exteriorPower (imageBundle K M hM s) (2 : ℤ) := by
  let : IsLocallyNoetherian (model K M hM) := model_locallyNoetherian K M hM
  let := bundle_rank K (modelInclusion K M hM)
  exact RankTwoSubsystemBundles.betaExteriorIso (originalMap K M hM s) hr

/-- A literal pair of the original image sections determines this
genuine global section of the genuine native determinant beta. -/
def pairBetaSection (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) : cohomologyOverField K (modelProjection K M hM) (beta K M hM s) 0 :=
  MukaiEvaluationChoices.cohomologyEquiv K (modelProjection K M hM)
    (betaExteriorIso K M hM s hr).symm 0 (pairExteriorSection K M hM s e)

omit [CharZero K] in
theorem pairBetaSection_formula (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) :
    pairBetaSection K M hM s hr e = cohomologyOverFieldMap K (modelProjection K M hM)
      (betaExteriorIso K M hM s hr).inv 0
      (ExteriorEvaluation.lambda K (modelProjection K M hM) (imageBundle K M hM s) 2
        (exteriorPower.ιMulti K 2 (imageSections K M hM s ∘ e))) := rfl

omit [CharZero K] in
/-- The actual integral curve supplies its actual generic point; rank
two there selects a genuine pair with nonzero global beta-section. -/
theorem exists_nonzero_pair_section (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    ∃ e : Fin 2 ↪ Fin 3, pairBetaSection K M hM s hr e ≠ 0 := by
  let : IsLocallyNoetherian (model K M hM) := model_locallyNoetherian K M hM
  let := bundle_rank K (modelInclusion K M hM)
  obtain ⟨e, he⟩ := RankTwoSubsystemWedge.exists_pairExteriorSection_ne_zero K
    (modelProjection K M hM) (originalMap K M hM s) hr (genericPoint (model K M hM))
  refine ⟨e, ?_⟩
  intro hz
  apply he
  exact (MukaiEvaluationChoices.cohomologyEquiv K (modelProjection K M hM)
    (betaExteriorIso K M hM s hr).symm 0).injective (hz.trans (map_zero _).symm)

variable [IsAlgClosed K]

/-- Actual existence, bundles, short exact sequences, canonical tensor
relation and a NONZERO original-pair determinant section are conclusions. -/
theorem exists_bundle_data :
    ∃ (s : Fin 3 → (Fin 6 → K))
      (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2),
      LinearIndependent K s ∧ LinearIndependent K (imageSections K M hM s) ∧
      LagrangianTripleDeterminantSection.determinantValue K
        (modelProjection K M hM) (modelInclusion K M hM) s = 0 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernelLine K M hM s) 1 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha K M hM s) 1 ∧
      SheafOfModules.IsInvertible (model K M hM).presheaf
        (model K M hM).ringCatSheaf.property (kernelLine K M hM s) ∧
      SheafOfModules.IsInvertible (model K M hM).presheaf
        (model K M hM).ringCatSheaf.property (alpha K M hM s) ∧
      SheafOfModules.IsInvertible (model K M hM).presheaf
        (model K M hM).ringCatSheaf.property (beta K M hM s) ∧
      (kernelSequence K M hM s).ShortExact ∧ (quotientSequence K M hM s).ShortExact ∧
      Nonempty (tensor (beta K M hM s) (alpha K M hM s) ≅
        Stacks.Duality.dualizingSheafOverField (modelProjection K M hM)) ∧
      ∃ e : Fin 2 ↪ Fin 3, pairBetaSection K M hM s hr e ≠ 0 := by
  obtain ⟨s, hs, himages, hdet, hr⟩ := MukaiDeterminantZeroSubsystem.exists_rank_two_subsystem K M hM
  have hR := ranks K M hM s hr
  exact ⟨s, hr, hs, imageSections_independent K M hM s himages, hdet,
    hR.1, hR.2.1, hR.2.2, kernelLine_isInvertible K M hM s hr,
    alpha_isInvertible K M hM s hr, beta_isInvertible K M hM s hr,
    kernelSequence_shortExact K M hM s, quotientSequence_shortExact K M hM s,
    ⟨betaTensorAlphaCanonicalIso K M hM s hr⟩, exists_nonzero_pair_section K M hM s hr⟩

end IntegralSmooth

variable [IsAlgClosed K]

/-- The actual canonical good open derives all geometry; no subsystem,
bundle, line, exactness, canonical relation or nonzero pair is assumed. -/
theorem exists_bundle_data_of_goodOpen
    (hg : LagrangianMatrixPointRows.matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen K) :
    letI : IsIntegral (model K M hM) := LagrangianGoodOpenRestriction.model_integral K M hM hg
    letI : SmoothOfRelativeDimension 1 (modelProjection K M hM) :=
      LagrangianGoodOpenRestriction.model_smooth K M hM hg
    ∃ (s : Fin 3 → (Fin 6 → K))
      (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2),
      LinearIndependent K s ∧ LinearIndependent K (imageSections K M hM s) ∧
      LagrangianTripleDeterminantSection.determinantValue K
        (modelProjection K M hM) (modelInclusion K M hM) s = 0 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernelLine K M hM s) 1 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha K M hM s) 1 ∧
      SheafOfModules.IsInvertible (model K M hM).presheaf
        (model K M hM).ringCatSheaf.property (kernelLine K M hM s) ∧
      SheafOfModules.IsInvertible (model K M hM).presheaf
        (model K M hM).ringCatSheaf.property (alpha K M hM s) ∧
      SheafOfModules.IsInvertible (model K M hM).presheaf
        (model K M hM).ringCatSheaf.property (beta K M hM s) ∧
      (kernelSequence K M hM s).ShortExact ∧ (quotientSequence K M hM s).ShortExact ∧
      Nonempty (tensor (beta K M hM s) (alpha K M hM s) ≅
        Stacks.Duality.dualizingSheafOverField (modelProjection K M hM)) ∧
      ∃ e : Fin 2 ↪ Fin 3, pairBetaSection K M hM s hr e ≠ 0 := by
  let : IsIntegral (model K M hM) := LagrangianGoodOpenRestriction.model_integral K M hM hg
  let : SmoothOfRelativeDimension 1 (modelProjection K M hM) :=
    LagrangianGoodOpenRestriction.model_smooth K M hM hg
  exact exists_bundle_data K M hM

end M9Native.LagrangianRankTwoSubsystemExistence

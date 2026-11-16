module

public import M9StacksIntegration.LagrangianOriginalSubsystemExclusions
public import M9StacksIntegration.LagrangianRankTwoQuotientSections
public import M9StacksIntegration.MukaiThreeGeneratorDeterminantSections
public import M9StacksIntegration.MukaiNonpentagonalResidualDegrees
public import M9StacksIntegration.MukaiCanonicalBundleFromNet
public import M9StacksIntegration.MukaiLemmaFiveOne

/-!
# The actual universal quotient on an actually nonpentagonal section

The original six-section system is injective and Semi on its literal
image. Its actual rank-two subsystem supplies the two genuine residual
lines. Original subsystem exclusions produce their three sections;
nonpentagonality and the actual canonical tensor relation then force
both residual degrees to be eight and their H0 dimensions to be three.
Actual three-generator recognition and Lemma 5.1 bound the rank-two
image's H0, so the original six-section injection is complete. Complete
Semi and global generation are derived for the literal original Q.

The no-degree-five and genus-nine hypotheses concern this actual curve.
They are not asserted for every transverse section here. A main-theorem
open restriction must obtain them from genuine geometric membership.
No residual degree, complete basis, six-section count or desired bundle
classification is supplied as an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
universe u

namespace M9Native.LagrangianNonpentagonalQuotientFactory

open LagrangianOrderedFibre LagrangianUniversalSections
open LagrangianRankTwoSubsystemBundles

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- Actual conditional factory for the original universal quotient.
Every complete-system property and both residual degrees are conclusions. -/
theorem isCanonicalGeneratedSemi_of_no_degree_five
    (hg : genus (modelProjection K M hM) = 9)
    (hnp : ¬ Nonempty (LinearSeries K (modelProjection K M hM)
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (modelProjection K M hM) 1).le 5 1)) :
    letI := model_isCurve K M hM
    letI := SmoothOfRelativeDimension.smooth 1 (modelProjection K M hM)
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi
      (modelProjection K M hM) (bundle K (modelInclusion K M hM)) := by
  classical
  let C := model K M hM
  let f := modelProjection K M hM
  let Q := bundle K (modelInclusion K M hM)
  letI := model_isCurve K M hM
  letI := SmoothOfRelativeDimension.smooth 1 f
  letI := isIso_globalSections_of_isAlgClosed K f
  letI := bundle_rank K (modelInclusion K M hM)
  let hdim : topologicalKrullDim C ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1).le
  obtain ⟨s,hs,himages,hdet,hr⟩ :=
    MukaiDeterminantZeroSubsystem.exists_rank_two_subsystem K M hM
  let F := imageBundle K M hM s
  let A := alpha K M hM s
  let B := beta K M hM s
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2 :=
    (ranks K M hM s hr).2.1
  letI := alpha_isInvertible K M hM s hr
  letI := beta_isInvertible K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 1 :=
    (ranks K M hM s hr).2.2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible C B
  letI := MukaiRecognitionHomBound.finite_bundle_H0 K f Q 3
  letI := MukaiRecognitionHomBound.finite_bundle_H0 K f F 2
  letI := MukaiRecognitionHomBound.finite_bundle_H0 K f A 1
  letI := MukaiRecognitionHomBound.finite_bundle_H0 K f B 1
  let qF : netFree C ⟶ F := factorThruImage (originalMap K M hM s)
  letI : Epi qF := (kernelSequence_shortExact K M hM s).epi_g
  let dB : topExterior F 2 ≅ B :=
    (LagrangianRankTwoSubsystemExistence.betaExteriorIso K M hM s hr).symm
  have hvan : ∀ a : F ⟶ structureModule C, a = 0 :=
    LagrangianOriginalSubsystemExclusions.image_hom_unit_eq_zero K M hM s hs hr
  have hB3 : 3 ≤ finrank K (cohomologyOverField K f B 0) :=
    MukaiThreeGeneratorDeterminantSections.three_le_h0_of_three_generators_on_curve
      K f F B qF dB hvan
  have hA3 : 3 ≤ finrank K (cohomologyOverField K f A 0) := by
    have h := (LinearMap.range (LagrangianRankTwoQuotientSections.alphaSections K M hM s)).finrank_le
    rw [LagrangianRankTwoQuotientSections.alphaSections_range_finrank K M hM s hs hr] at h
    exact h
  let hres : tensor B A ≅ Stacks.Duality.dualizingSheafOverField f :=
    betaTensorAlphaCanonicalIso K M hM s hr
  obtain ⟨hB8,hA8,hB0,hA0⟩ := MukaiNonpentagonalResidualDegrees.degrees_and_h0
    f hdim hg hnp B A hres hB3 hA3
  let bB : Basis (ULift.{u} (Fin 3)) K (cohomologyOverField K f B 0) :=
    (Module.finBasisOfFinrankEq K (cohomologyOverField K f B 0) hB0).reindex Equiv.ulift.symm
  let Eβ : LinearSeries K f hdim 8 2 :=
    { L := B
      isInvertible := inferInstance
      degree_eq := hB8
      V := ⊤
      finrank_eq := by simpa using hB0 }
  let eF : F ≅ dualSpan B (MukaiDualSpanSections.completeNetSections f B bB) :=
    MukaiThreeGeneratorRecognition.dualSpanIso_of_three_generators K f F B qF dB hvan bB
  have hFQ : finrank K (cohomologyOverField K f
      (dualSpan B (MukaiDualSpanSections.completeNetSections f B bB)) 0) = 3 :=
    (MukaiLemmaFiveOne.lemma_five_one_for_complete_basis f hdim hg hnp Eβ bB A hA8).1
  have hF0 : finrank K (cohomologyOverField K f F 0) = 3 :=
    (MukaiEvaluationChoices.cohomologyEquiv K f eF 0).finrank_eq.trans hFQ
  letI : Module.Finite K
      (cohomologyOverField K f (quotientSequence K M hM s).X₁ 0) := by
    change Module.Finite K (cohomologyOverField K f F 0)
    infer_instance
  letI : Module.Finite K
      (cohomologyOverField K f (quotientSequence K M hM s).X₂ 0) := by
    change Module.Finite K (cohomologyOverField K f Q 0)
    infer_instance
  letI : Module.Finite K
      (cohomologyOverField K f (quotientSequence K M hM s).X₃ 0) := by
    change Module.Finite K (cohomologyOverField K f A 0)
    infer_instance
  have hbnd := MukaiBundleUniqueness.finrank_H0_le_add K f
    (quotientSequence_shortExact K M hM s)
  change finrank K (cohomologyOverField K f Q 0) ≤
    finrank K (cohomologyOverField K f F 0) + finrank K (cohomologyOverField K f A 0) at hbnd
  rw [hF0,hA0] at hbnd
  have hj : Function.Injective (sectionMap K f (modelInclusion K M hM)) := by
    apply LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank
      K f (modelInclusion K M hM) rfl
    rw [LagrangianModelRestriction.primitiveRestriction_range_finrank K M hM]
    norm_num
  have hlow : 6 ≤ finrank K (cohomologyOverField K f Q 0) := by
    simpa using LinearMap.finrank_le_finrank_of_injective hj
  have h6 : finrank K (cohomologyOverField K f Q 0) = 6 := le_antisymm hbnd hlow
  have htop : LinearMap.range (sectionMap K f (modelInclusion K M hM)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hj,h6]
    simp
  have hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f Q 3 := by
    apply (MukaiSemiIrreducible.completeSemiIrreducible_iff_top K f Q 3).mpr
    have h := LagrangianOriginalSubsystemSemi.originalSubsystem_semi K M hM
    change MukaiSemiIrreducible.SemiIrreducible K f Q 3
      (LinearMap.range (sectionMap K f (modelInclusion K M hM))) at h
    rw [htop] at h
    exact h
  have hgen : MukaiSemiIrreducible.GloballyGenerated Q := by
    letI : Epi (quotientMap K (modelInclusion K M hM)) :=
      (quotient K (modelInclusion K M hM)).map_epi
    exact ⟨(_root_.SheafOfModules.free.generatingSections
      (R := C.ringCatSheaf) (ULift.{u} (Fin 6))).ofEpi
        (quotientMap K (modelInclusion K M hM))⟩
  exact ⟨inferInstance,h6,⟨quotientDeterminantCanonicalIso K M hM⟩,hgen,hsemi⟩

end M9Native.LagrangianNonpentagonalQuotientFactory

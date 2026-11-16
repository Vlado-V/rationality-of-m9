module

public import M9StacksIntegration.RankTwoSubsystemBundles
public import M9StacksIntegration.MukaiDeterminantZeroSubsystem
public import M9StacksIntegration.LagrangianFiveSectionAdjunction
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials

/-!
# Actual bundles of the original rank-two subsystem

The objects are the categorical kernel, image and cokernel of the literal
original three-section evaluation. Actual integral smooth curve geometry
supplies the reducedness and local Noetherianity required by constant-rank
descent. The original five-section adjunction and native canonical-line
comparison identify the determinant of Q with the actual canonical sheaf.
The quotient short exact sequence therefore constructs beta tensor alpha
isomorphic to that canonical sheaf. No quotient degree, line, exactness or
determinant-comparison data is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.MukaiBundleDeterminant

namespace M9Native.LagrangianRankTwoSubsystemBundles
open LagrangianOrderedFibre LagrangianUniversalSections LagrangianUniversalTriples
universe u
variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

abbrev originalMap (s : Fin 3 → (Fin 6 → K)) :=
  evaluation K (modelProjection K M hM) (modelInclusion K M hM) s

abbrev kernelLine (s : Fin 3 → (Fin 6 → K)) :=
  RankTwoSubsystemBundles.kernelLine (originalMap K M hM s)

abbrev imageBundle (s : Fin 3 → (Fin 6 → K)) :=
  RankTwoSubsystemBundles.imageBundle (originalMap K M hM s)

abbrev alpha (s : Fin 3 → (Fin 6 → K)) :=
  RankTwoSubsystemBundles.alpha (originalMap K M hM s)

abbrev beta (s : Fin 3 → (Fin 6 → K)) :=
  RankTwoSubsystemBundles.beta (originalMap K M hM s)

abbrev kernelSequence (s : Fin 3 → (Fin 6 → K)) :=
  RankTwoSubsystemBundles.kernelSequence (originalMap K M hM s)

abbrev quotientSequence (s : Fin 3 → (Fin 6 → K)) :=
  RankTwoSubsystemBundles.quotientSequence (originalMap K M hM s)

omit [CharZero K] in
theorem kernelSequence_shortExact (s : Fin 3 → (Fin 6 → K)) :
    (kernelSequence K M hM s).ShortExact :=
  RankTwoSubsystemBundles.kernelSequence_shortExact (originalMap K M hM s)

omit [CharZero K] in
theorem quotientSequence_shortExact (s : Fin 3 → (Fin 6 → K)) :
    (quotientSequence K M hM s).ShortExact :=
  RankTwoSubsystemBundles.quotientSequence_shortExact (originalMap K M hM s)

/-- Properness of the literal model follows from the constructed
original ordered-cut isomorphism, preserving the actual base map. -/
theorem model_proper : IsProper (modelProjection K M hM) := by
  have hbase : (cutIsoModel K M hM).hom ≫ modelProjection K M hM =
      LagrangianTransverseRestriction.curveProjection K M := cutIsoModel_hom_base K M hM
  have h : (cutIsoModel K M hM).inv ≫ LagrangianTransverseRestriction.curveProjection K M =
      modelProjection K M hM := by
    rw [← hbase, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [← h]
  infer_instance

attribute [instance] model_proper

section Smooth
variable [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

omit [CharZero K] in
theorem model_locallyNoetherian : IsLocallyNoetherian (model K M hM) := by
  let : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  exact isLocallyNoetherian_of_isRegular
    (isRegular_of_smooth_over_field (modelProjection K M hM))

variable [IsIntegral (model K M hM)]

theorem model_isCurve : IsCurve K (modelProjection K M hM) := by
  let : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  exact (isCurve_iff K (modelProjection K M hM)).mpr
    ⟨⟨⟩, topologicalKrullDim_eq_of_smoothOfRelativeDimension (modelProjection K M hM) 1⟩

/-- Reducedness comes from the original integral curve, and local
Noetherianity comes from its actual smooth structural morphism. -/
theorem ranks (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernelLine K M hM s) 1 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha K M hM s) 1 := by
  let : IsLocallyNoetherian (model K M hM) := model_locallyNoetherian K M hM
  let := bundle_rank K (modelInclusion K M hM)
  exact RankTwoSubsystemBundles.ranks (originalMap K M hM s) hr

theorem kernelLine_isInvertible (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    SheafOfModules.IsInvertible (model K M hM).presheaf
      (model K M hM).ringCatSheaf.property (kernelLine K M hM s) := by
  let : IsLocallyNoetherian (model K M hM) := model_locallyNoetherian K M hM
  let := bundle_rank K (modelInclusion K M hM)
  exact RankTwoSubsystemBundles.kernelLine_isInvertible (originalMap K M hM s) hr

theorem alpha_isInvertible (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    SheafOfModules.IsInvertible (model K M hM).presheaf
      (model K M hM).ringCatSheaf.property (alpha K M hM s) := by
  let : IsLocallyNoetherian (model K M hM) := model_locallyNoetherian K M hM
  let := bundle_rank K (modelInclusion K M hM)
  exact RankTwoSubsystemBundles.alpha_isInvertible (originalMap K M hM s) hr

theorem beta_isInvertible (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    SheafOfModules.IsInvertible (model K M hM).presheaf
      (model K M hM).ringCatSheaf.property (beta K M hM s) := by
  let : IsLocallyNoetherian (model K M hM) := model_locallyNoetherian K M hM
  let := bundle_rank K (modelInclusion K M hM)
  exact RankTwoSubsystemBundles.beta_isInvertible (originalMap K M hM s) hr

/-- Actual adjunction on the original five-section model identifies the
original quotient's determinant with the actual canonical sheaf. -/
def quotientDeterminantCanonicalIso :
    Scheme.Modules.exteriorPower (bundle K (modelInclusion K M hM)) (3 : ℤ) ≅
      Stacks.Duality.dualizingSheafOverField (modelProjection K M hM) := by
  let : IsCurve K (modelProjection K M hM) := model_isCurve K M hM
  let : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  exact (LagrangianPullback.exteriorPullbackIso (modelInclusion K M hM)
      (LagrangianPluckerQuotient.quotientOnLG K).target 3).symm ≪≫
    (LagrangianFiveSectionAdjunction.differentialsIsoCurveLine K
      (LagrangianFibreFiveSection.fiveSection K M hM)).symm ≪≫
    (SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso (modelProjection K M hM)).symm

/-- The actual image/cokernel sequence yields the canonical residual
tensor relation, without a supplied determinant or canonical isomorphism. -/
def betaTensorAlphaCanonicalIso (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    tensor (beta K M hM s) (alpha K M hM s) ≅
      Stacks.Duality.dualizingSheafOverField (modelProjection K M hM) := by
  let : IsLocallyNoetherian (model K M hM) := model_locallyNoetherian K M hM
  let := bundle_rank K (modelInclusion K M hM)
  exact RankTwoSubsystemBundles.betaTensorAlphaIso (originalMap K M hM s) hr ≪≫
    quotientDeterminantCanonicalIso K M hM

end Smooth
end M9Native.LagrangianRankTwoSubsystemBundles

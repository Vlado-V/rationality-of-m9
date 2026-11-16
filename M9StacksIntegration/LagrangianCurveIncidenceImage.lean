module

public import M9StacksIntegration.LagrangianCurveIncidenceBetaFactor
public import M9StacksIntegration.LagrangianIncidenceCurveBaseChange
public import M9StacksIntegration.FreeTwoPairIncidenceBaseChange
public import M9StacksIntegration.FreeTwoPairIncidenceSubbundle
public import M9StacksIntegration.RankTwoSelectedPairIncidenceIso

/-! The actual C-only original Q-incidence is the actual incidence
of the actual rank-two image evaluation. Full ideals are retained by
projective base change and by the genuine image/cokernel subbundle. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.LagrangianCurveIncidenceImage
open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles LagrangianBetaRankDrop
open LagrangianUniversalSections
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart FreeTwoProjectiveCharts
open LagrangianCurveIncidenceBetaFactor
variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]
  (s : Fin 3 → (Fin 6 → K))
  (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
  (e : Fin 2 ↪ Fin 3)

abbrev imageEvaluation := factorThruImage (originalMap K M hM s)
abbrev imageSections := RankTwoSelectedPairIncidenceIso.selectedSections (imageEvaluation K M hM s) e

def quotientSections : Fin 2 → Γ(bundle K (modelInclusion K M hM),⊤) :=
  fun k => pullbackGlobalSections (modelInclusion K M hM) (quotientOnLG K).target
    (LagrangianArbitraryPlaneIncidence.originalSection K (s ∘ e) k)

theorem imageSections_maps (k : Fin 2) :
    (image.ι (originalMap K M hM s)).app ⊤ (imageSections K M hM s e k) =
      quotientSections K M hM s e k := by
  have h := congrArg (fun z => z.app ⊤ (freeBasisSection (model K M hM) 3 (e k)))
    (image.fac (originalMap K M hM s))
  exact h.trans ((MukaiEvaluationMatrix.evaluation_basisSection K (modelProjection K M hM)
    (bundle K (modelInclusion K M hM))
    (fun i => LagrangianUniversalSections.sectionMap K (modelProjection K M hM)
      (modelInclusion K M hM) (s i)) (e k)).trans
        (LagrangianArbitraryPairPullback.originalSection_pullback K (modelInclusion K M hM)
          (s ∘ e) k).symm)

def quotientIncidenceIsoCurve :
    FreeTwoPairIncidence.space (model K M hM) (bundle K (modelInclusion K M hM))
      (quotientSections K M hM s e) ≅ curveIncidence K M hM s e :=
  LagrangianIncidenceCurveBaseChange.zeroIso K M hM s e

@[reassoc]
theorem quotientIncidenceIsoCurve_hom_fst : (quotientIncidenceIsoCurve K M hM s e).hom ≫
    pullback.fst _ _ = FreeTwoPairIncidence.toBase (model K M hM)
      (bundle K (modelInclusion K M hM)) (quotientSections K M hM s e) :=
  LagrangianIncidenceCurveBaseChange.zeroIso_hom_fst K M hM s e

theorem quotientSections_eq : quotientSections K M hM s e =
    FreeTwoPairIncidenceSubbundle.imageSections (model K M hM) (quotientSequence K M hM s)
      (imageSections K M hM s e) := by
  funext k
  exact (imageSections_maps K M hM s e k).symm

include hr in
theorem quotientImageIdeal_eq :
    FreeTwoPairIncidence.ideal (model K M hM) (bundle K (modelInclusion K M hM))
      (quotientSections K M hM s e) =
    FreeTwoPairIncidence.ideal (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e) := by
  have hR := ranks K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 := hR.2.1
  letI := bundle_rank K (modelInclusion K M hM)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha K M hM s) 1 := hR.2.2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientSequence K M hM s).X₁ 2 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2
    exact hR.2.1
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientSequence K M hM s).X₂ 3 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (bundle K (modelInclusion K M hM)) 3
    exact bundle_rank K (modelInclusion K M hM)
  exact (congrArg (FreeTwoPairIncidence.ideal (model K M hM) (bundle K (modelInclusion K M hM)))
    (quotientSections_eq K M hM s e)).trans
      (FreeTwoPairIncidenceSubbundle.ideal_eq (model K M hM) (quotientSequence K M hM s)
        (quotientSequence_shortExact K M hM s)
        (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (alpha K M hM s) 1)
        2 3 (imageSections K M hM s e))

def quotientIncidenceIsoImage :
    FreeTwoPairIncidence.space (model K M hM) (bundle K (modelInclusion K M hM))
      (quotientSections K M hM s e) ≅
    FreeTwoPairIncidence.space (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e) :=
  eqToIso (congrArg (fun I : (projectiveBundleSpace (model K M hM)).IdealSheafData => I.subscheme)
    (quotientImageIdeal_eq K M hM s hr e))

@[reassoc]
theorem quotientIncidenceIsoImage_hom_toBase : (quotientIncidenceIsoImage K M hM s hr e).hom ≫
    FreeTwoPairIncidence.toBase (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e) =
      FreeTwoPairIncidence.toBase (model K M hM) (bundle K (modelInclusion K M hM))
        (quotientSections K M hM s e) := by
  simpa only [quotientIncidenceIsoImage,FreeTwoPairIncidence.toBase,Category.assoc] using
    congrArg (· ≫ projectiveBundleProjection (model K M hM))
      (LagrangianMatrixChart.eqToIso_subscheme_ι _ _ (quotientImageIdeal_eq K M hM s hr e))

def curveIncidenceIsoImage : curveIncidence K M hM s e ≅
    FreeTwoPairIncidence.space (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e) :=
  (quotientIncidenceIsoCurve K M hM s e).symm ≪≫ quotientIncidenceIsoImage K M hM s hr e

@[reassoc]
theorem curveIncidenceIsoImage_hom_toBase : (curveIncidenceIsoImage K M hM s hr e).hom ≫
    FreeTwoPairIncidence.toBase (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e) =
      pullback.fst _ _ := by
  simp only [curveIncidenceIsoImage,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [quotientIncidenceIsoImage_hom_toBase]
  apply (cancel_epi (quotientIncidenceIsoCurve K M hM s e).hom).mp
  rw [Iso.hom_inv_id_assoc,quotientIncidenceIsoCurve_hom_fst]

end M9Native.LagrangianCurveIncidenceImage

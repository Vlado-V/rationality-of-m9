module

public import M9StacksIntegration.LagrangianCurveIncidenceImage
public import M9StacksIntegration.MonoFactorIsIso

/-! The actual original C-only incidence is isomorphic to the FULL
native beta zero scheme. The inverse is derived from the original
rank-two evaluation on all scheme tests. No finiteness, degree, length,
class, reduced-support identification, or desired isomorphism is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf
  M9Native.RankTwoSubsystemBundles.imageBundle
namespace M9Native.LagrangianSelectedPairIncidenceIso
open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles LagrangianBetaRankDrop
open LagrangianUniversalSections
open LagrangianCurveIncidenceBetaFactor LagrangianCurveIncidenceImage
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]
  (s : Fin 3 → (Fin 6 → K))
  (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
  (e : Fin 2 ↪ Fin 3)

abbrev imageWedge := wedgeSection (model K M hM) (imageBundle K M hM s)
  (imageSections K M hM s e 0) (imageSections K M hM s e 1)

theorem imageWedge_maps :
    (Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ)).app ⊤
      (imageWedge K M hM s e) =
    LagrangianArbitraryPairPullback.pairSection K (modelInclusion K M hM) (s ∘ e) := by
  simp only [imageWedge,LagrangianRankTwoSubsystemBundles.imageBundle,
    RankTwoSubsystemBundles.imageBundle,imageSections,
    RankTwoSelectedPairIncidenceIso.selectedSections,imageEvaluation]
  rw [← LagrangianGrassmannian.exteriorPowerMap_eq_native,
    LagrangianGrassmannian.exteriorPowerMap_wedgeSection]
  have h0 := imageSections_maps K M hM s e 0
  have h1 := imageSections_maps K M hM s e 1
  simp only [imageSections,RankTwoSelectedPairIncidenceIso.selectedSections,imageEvaluation] at h0 h1
  rw [h0,h1,LagrangianArbitraryPairPullback.pairSection_eq_wedge]
  simp only [quotientSections,LagrangianArbitraryPairPullback.originalSection_pullback]

include hr in
theorem exteriorImage_universallyMono {T : Scheme.{u}} (f : T ⟶ model K M hM) :
    Mono ((Scheme.Modules.pullback f).map
      (Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ))) := by
  have hR := ranks K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha K M hM s) 1 := hR.2.2
  exact ExteriorSubbundleUniversalMono.mono_pullback_exteriorPowerMap
    (quotientSequence K M hM s) (quotientSequence_shortExact K M hM s)
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (alpha K M hM s) 1) 2 f

theorem beta_originalSection_zero :
    pullbackGlobalSections (nativeBetaIdeal K M hM s hr e).subschemeι (beta K M hM s)
      (betaSection K M hM s hr e) = 0 := by
  letI := beta_rank K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (beta K M hM s) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  apply (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (beta K M hM s) 1 (betaSection K M hM s hr e) (nativeBetaIdeal K M hM s hr e).subschemeι).mpr
  rw [← NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal]
  exact ⟨𝟙 _,by simp⟩

theorem beta_imageWedge_zero :
    pullbackGlobalSections (nativeBetaIdeal K M hM s hr e).subschemeι
      (Scheme.Modules.exteriorPower (imageBundle K M hM s) (2 : ℤ)) (imageWedge K M hM s e) = 0 := by
  have hzero : pullbackGlobalSections (nativeBetaIdeal K M hM s hr e).subschemeι
      (Scheme.Modules.exteriorPower (bundle K (modelInclusion K M hM)) (2 : ℤ))
      ((Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ)).app ⊤
        (imageWedge K M hM s e)) = 0 := by
    have hb := betaInclusion_section K M hM s hr e
    simp only [LagrangianBetaRankDrop.originalPair] at hb
    rw [imageWedge_maps,← hb]
    rw [← SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
      beta_originalSection_zero,map_zero]
  exact (SectionZeroSubbundle.pullback_image_eq_zero_iff
    (Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ))
    (fun f => exteriorImage_universallyMono K M hM s hr f) (imageWedge K M hM s e)
      (nativeBetaIdeal K M hM s hr e).subschemeι).mp hzero

theorem beta_pulled_pair_wedge_zero :
    wedgeSection (nativeBetaIdeal K M hM s hr e).subscheme
      ((Scheme.Modules.pullback (nativeBetaIdeal K M hM s hr e).subschemeι).obj (imageBundle K M hM s))
      (RankTwoSelectedPairIncidenceIso.selectedSections
        (RankTwoSelectedPairIncidenceIso.pulledEvaluation (imageEvaluation K M hM s)
          (nativeBetaIdeal K M hM s hr e).subschemeι) e 0)
      (RankTwoSelectedPairIncidenceIso.selectedSections
        (RankTwoSelectedPairIncidenceIso.pulledEvaluation (imageEvaluation K M hM s)
          (nativeBetaIdeal K M hM s hr e).subschemeι) e 1) = 0 := by
  have hR := ranks K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 := hR.2.1
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image (originalMap K M hM s)) 2 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2
    exact hR.2.1
  change wedgeSection (nativeBetaIdeal K M hM s hr e).subscheme _
    ((RankTwoSelectedPairIncidenceIso.pulledEvaluation (imageEvaluation K M hM s)
      (nativeBetaIdeal K M hM s hr e).subschemeι).app ⊤
        (freeBasisSection (nativeBetaIdeal K M hM s hr e).subscheme 3 (e 0)))
    ((RankTwoSelectedPairIncidenceIso.pulledEvaluation (imageEvaluation K M hM s)
      (nativeBetaIdeal K M hM s hr e).subschemeι).app ⊤
        (freeBasisSection (nativeBetaIdeal K M hM s hr e).subscheme 3 (e 1))) = 0
  rw [RankTwoSelectedPairIncidenceIso.pulledEvaluation_basis,
    RankTwoSelectedPairIncidenceIso.pulledEvaluation_basis,
    ← LagrangianGrassmannian.exteriorPullback_wedgeSection]
  have h := congrArg ((LagrangianPullback.exteriorPullbackIso
    (nativeBetaIdeal K M hM s hr e).subschemeι (imageBundle K M hM s) 2).hom.app ⊤)
    (beta_imageWedge_zero K M hM s hr e)
  have hz := Scheme.Modules.Hom.app_smul
    (LagrangianPullback.exteriorPullbackIso
      (nativeBetaIdeal K M hM s hr e).subschemeι (imageBundle K M hM s) 2).hom
    (0 : Γ((nativeBetaIdeal K M hM s hr e).subscheme,⊤))
    (0 : Γ((Scheme.Modules.pullback (nativeBetaIdeal K M hM s hr e).subschemeι).obj
      (Scheme.Modules.exteriorPower (imageBundle K M hM s) (2 : ℤ)),⊤))
  simp only [zero_smul] at hz
  rw [hz] at h
  simpa only [imageWedge,imageSections,RankTwoSelectedPairIncidenceIso.selectedSections,
    LagrangianRankTwoSubsystemBundles.imageBundle,RankTwoSubsystemBundles.imageBundle,map_zero] using h

theorem beta_baseChange_projection_isIso :
    IsIso (pullback.fst (nativeBetaIdeal K M hM s hr e).subschemeι
      (FreeTwoPairIncidence.toBase (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e))) := by
  have hR := ranks K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 := hR.2.1
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image (originalMap K M hM s)) 2 := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2
    exact hR.2.1
  let g := (nativeBetaIdeal K M hM s hr e).subschemeι
  let Fg := (Scheme.Modules.pullback g).obj (imageBundle K M hM s)
  letI := isFiniteLocallyFreeOfRank_pullback g (imageBundle K M hM s) 2
  letI := isFiniteLocallyFreeOfRank_pullback g (image (originalMap K M hM s)) 2
  have hloc := RankTwoSelectedPairIncidenceIso.projection_isIso
    (RankTwoSelectedPairIncidenceIso.pulledEvaluation (imageEvaluation K M hM s) g) e
      (beta_pulled_pair_wedge_zero K M hM s hr e)
  have hs : FreeTwoPairIncidenceBaseChange.sections g (imageBundle K M hM s) Fg (Iso.refl Fg)
      (imageSections K M hM s e) = RankTwoSelectedPairIncidenceIso.selectedSections
        (RankTwoSelectedPairIncidenceIso.pulledEvaluation (imageEvaluation K M hM s) g) e := by
    funext k
    exact (RankTwoSelectedPairIncidenceIso.pulledEvaluation_basis (imageEvaluation K M hM s) g (e k)).symm
  let d := FreeTwoPairIncidenceBaseChange.baseChangeIso g (imageBundle K M hM s) Fg
    (Iso.refl Fg) 2 (imageSections K M hM s e)
  letI : IsIso (d.hom ≫ pullback.fst g
      (FreeTwoPairIncidence.toBase (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e))) := by
    rw [FreeTwoPairIncidenceBaseChange.baseChangeIso_hom_fst,hs]
    exact hloc
  exact IsIso.of_isIso_comp_left d.hom _

def imageIncidenceToBeta :
    FreeTwoPairIncidence.space (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e) ⟶
      (nativeBetaIdeal K M hM s hr e).subscheme :=
  (curveIncidenceIsoImage K M hM s hr e).inv ≫ curveIncidenceToBeta K M hM s hr e

@[reassoc]
theorem imageIncidenceToBeta_inclusion : imageIncidenceToBeta K M hM s hr e ≫
    (nativeBetaIdeal K M hM s hr e).subschemeι =
      FreeTwoPairIncidence.toBase (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e) := by
  rw [imageIncidenceToBeta,Category.assoc,curveIncidenceToBeta_inclusion]
  apply (cancel_epi (curveIncidenceIsoImage K M hM s hr e).hom).mp
  rw [Iso.hom_inv_id_assoc,curveIncidenceIsoImage_hom_toBase]

theorem curveIncidenceToBeta_isIso : IsIso (curveIncidenceToBeta K M hM s hr e) := by
  letI := beta_baseChange_projection_isIso K M hM s hr e
  letI : IsIso (imageIncidenceToBeta K M hM s hr e) :=
    MonoFactorIsIso.isIso_factor (nativeBetaIdeal K M hM s hr e).subschemeι
      (imageIncidenceToBeta K M hM s hr e)
      (FreeTwoPairIncidence.toBase (model K M hM) (imageBundle K M hM s) (imageSections K M hM s e))
      (imageIncidenceToBeta_inclusion K M hM s hr e)
  letI : IsIso ((curveIncidenceIsoImage K M hM s hr e).inv ≫
      curveIncidenceToBeta K M hM s hr e) := by
    change IsIso (imageIncidenceToBeta K M hM s hr e)
    infer_instance
  exact IsIso.of_isIso_comp_left (curveIncidenceIsoImage K M hM s hr e).inv
    (curveIncidenceToBeta K M hM s hr e)

def curveIncidenceIsoBeta :
    pullback (modelInclusion K M hM)
      (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e)) ≅
      (Stacks.Chow.zeroSchemeOfSection (model K M hM) (beta K M hM s)
        (betaSection K M hM s hr e)).subscheme := by
  letI := curveIncidenceToBeta_isIso K M hM s hr e
  exact asIso (curveIncidenceToBeta K M hM s hr e)

@[reassoc]
theorem curveIncidenceIsoBeta_hom_fst : (curveIncidenceIsoBeta K M hM s hr e).hom ≫
    (Stacks.Chow.zeroSchemeOfSection (model K M hM) (beta K M hM s)
      (betaSection K M hM s hr e)).subschemeι = pullback.fst _ _ :=
  curveIncidenceToBeta_inclusion K M hM s hr e

end M9Native.LagrangianSelectedPairIncidenceIso

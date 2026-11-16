module

public import M9StacksIntegration.LagrangianRankTwoSubsystemExistence
public import M9StacksIntegration.LagrangianArbitraryPairPullback
public import M9StacksIntegration.SectionZeroSubbundle

/-!
# The actual beta zero scheme is the full original pair rank-drop pullback

The map from the genuine determinant of the actual rank-two image into
the second exterior power of the original Q remains monic under every
scheme pullback. This follows from the genuine image/cokernel sequence
and its derived locally free quotient. The same original pair of the
same three original sections is retained throughout. No degree, class,
symplectic-plane or equality-of-zero-ideals premise is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianBetaRankDrop
open LagrangianOrderedFibre LagrangianUniversalSections LagrangianRankTwoSubsystemBundles
open LagrangianRankTwoSubsystemExistence SectionZeroIdealFactorization
variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- The two literal original six-vectors selected by the actual pair. -/
def originalPair (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    LagrangianArbitraryPlaneIncidence.PlaneFrame K := s ∘ e

omit [CharZero K] in
theorem originalPair_independent (s : Fin 3 → (Fin 6 → K))
    (hs : LinearIndependent K s) (e : Fin 2 ↪ Fin 3) :
    LinearIndependent K (originalPair K s e) := hs.comp e e.injective

/-- The actual global beta section corresponding to the selected actual
H0 section of the genuine determinant, rather than an ad hoc line. -/
def betaSection (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) : Γ(beta K M hM s, ⊤) :=
  (cohomologyOverFieldZeroLinearIso K (modelProjection K M hM) (beta K M hM s)).hom
    (pairBetaSection K M hM s hr e)

/-- This inclusion is induced by the actual image inclusion of the
original evaluation and the actual native determinant comparison. -/
def betaInclusion (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    beta K M hM s ⟶ Scheme.Modules.exteriorPower (bundle K (modelInclusion K M hM)) (2 : ℤ) :=
  (betaExteriorIso K M hM s hr).hom ≫
    Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ)

theorem beta_rank (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (beta K M hM s) 1 := by
  letI := beta_isInvertible K M hM s hr
  exact SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (model K M hM) (beta K M hM s)

/-- Every pullback, even to a nonreduced test scheme, retains this
actual monomorphism; no universal-injectivity hypothesis is supplied. -/
theorem betaInclusion_pullback_mono (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    {T : Scheme.{u}} (f : T ⟶ model K M hM) :
    Mono ((Scheme.Modules.pullback f).map (betaInclusion K M hM s hr)) := by
  have hR := ranks K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (alpha K M hM s) 1 := hR.2.2
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (alpha K M hM s) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  letI : Mono ((Scheme.Modules.pullback f).map
      (Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ))) :=
    ExteriorSubbundleUniversalMono.mono_pullback_exteriorPowerMap
      (quotientSequence K M hM s) (quotientSequence_shortExact K M hM s)
      (by change SheafOfModules.IsFiniteLocallyFree.{u,u,u} (alpha K M hM s); infer_instance) 2 f
  rw [betaInclusion, Functor.map_comp]
  infer_instance

/-- The inclusion sends the SAME actual beta section to the SAME pair
of ORIGINAL Q sections under the actual H0/global-section comparison. -/
theorem betaInclusion_section (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) :
    (betaInclusion K M hM s hr).app ⊤ (betaSection K M hM s hr e) =
      LagrangianArbitraryPairPullback.pairSection K (modelInclusion K M hM)
        (originalPair K s e) := by
  have hi := (MukaiEvaluationChoices.cohomologyEquiv K (modelProjection K M hM)
    (betaExteriorIso K M hM s hr).symm 0).left_inv
      (pairExteriorSection K M hM s e)
  change cohomologyOverFieldMap K (modelProjection K M hM)
    (betaExteriorIso K M hM s hr).hom 0 (pairBetaSection K M hM s hr e) =
      pairExteriorSection K M hM s e at hi
  change (Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ)).app ⊤
    ((betaExteriorIso K M hM s hr).hom.app ⊤ (betaSection K M hM s hr e)) = _
  rw [betaSection, ← cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap, hi]
  refine (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap K (modelProjection K M hM)
    (Scheme.Modules.exteriorPowerMap (image.ι (originalMap K M hM s)) (2 : ℤ))
    (pairExteriorSection K M hM s e)).symm.trans ?_
  rw [pairExteriorSection_maps_to_original]
  rfl

/-- The FULL beta section-zero ideal is the FULL pullback of the actual
original pair rank-drop ideal, retaining all scheme structure. -/
theorem betaZeroIdeal_eq_rankDrop_comap (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) :
    sectionZeroIdeal (model K M hM) (beta K M hM s) (betaSection K M hM s hr e) =
      (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (originalPair K s e)).comap
        (modelInclusion K M hM) := by
  letI := beta_rank K M hM s hr
  letI := bundle_rank K (modelInclusion K M hM)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower (bundle K (modelInclusion K M hM)) (2 : ℤ)) 3 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      (bundle K (modelInclusion K M hM)) 3 2
  rw [LagrangianArbitraryPairPullback.rankDropIdeal_comap_eq]
  have h := SectionZeroSubbundle.sectionZeroIdeal_eq_of_universallyMono
    (betaInclusion K M hM s hr) 1 3 (fun f => betaInclusion_pullback_mono K M hM s hr f)
    (betaSection K M hM s hr e)
  rw [betaInclusion_section] at h
  exact h.symm

/-- The SAME ideal equality for the literal native Chow zero scheme. -/
theorem nativeBetaZeroIdeal_eq_rankDrop_comap (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) :
    Stacks.Chow.zeroSchemeOfSection (model K M hM) (beta K M hM s)
      (betaSection K M hM s hr e) =
      (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (originalPair K s e)).comap
        (modelInclusion K M hM) := by
  letI := beta_rank K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (beta K M hM s) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  rw [NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal]
  exact betaZeroIdeal_eq_rankDrop_comap K M hM s hr e

omit [CharZero K] in
theorem betaSection_ne_zero (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) (he : pairBetaSection K M hM s hr e ≠ 0) :
    betaSection K M hM s hr e ≠ 0 := by
  intro hz
  apply he
  exact (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso K (modelProjection K M hM) (beta K M hM s)).hom).injective
      (hz.trans (map_zero _).symm)

def betaZeroIdeal (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) : (model K M hM).IdealSheafData :=
  sectionZeroIdeal (model K M hM) (beta K M hM s) (betaSection K M hM s hr e)

abbrev betaZero (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) : Scheme.{u} := (betaZeroIdeal K M hM s hr e).subscheme

/-- Actual scheme isomorphism to the actual rank-drop Cartesian pullback. -/
def betaZeroIsoRankDropPullback (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) : betaZero K M hM s hr e ≅
      pullback (modelInclusion K M hM)
        (LagrangianArbitraryPlaneIncidence.rankDropInclusion K (originalPair K s e)) :=
  eqToIso (congrArg (fun I : (model K M hM).IdealSheafData => I.subscheme)
    (betaZeroIdeal_eq_rankDrop_comap K M hM s hr e)) ≪≫
    (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (originalPair K s e)).comapIso
      (modelInclusion K M hM)

@[reassoc]
theorem betaZeroIsoRankDropPullback_hom_fst (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) :
    (betaZeroIsoRankDropPullback K M hM s hr e).hom ≫ pullback.fst _ _ =
      (betaZeroIdeal K M hM s hr e).subschemeι := by
  rw [betaZeroIsoRankDropPullback, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact LagrangianMatrixChart.eqToIso_subscheme_ι _ _
    (betaZeroIdeal_eq_rankDrop_comap K M hM s hr e)

end M9Native.LagrangianBetaRankDrop

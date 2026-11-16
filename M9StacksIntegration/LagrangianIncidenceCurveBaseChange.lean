module

public import M9StacksIntegration.LagrangianCurveIncidenceBetaFactor
public import M9StacksIntegration.NativeFramedPairBaseChange
public import M9StacksIntegration.PairIncidencePullbackTerm
public import M9StacksIntegration.FreeTwoPairIncidence
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist

/-! Direct base change of the ORIGINAL native LG pairing incidence to
the ORIGINAL C coefficient projective bundle. No global comparison
with a second LG projective-bundle model is performed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.LagrangianIncidenceCurveBaseChange
open LagrangianOrderedFibre LagrangianUniversalSections LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianMatrixChart FreeTwoProjectiveCharts LagrangianCurveIncidenceBetaFactor
variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

abbrev coefficientFrame : LagrangianArbitraryPlaneIncidence.planeSource K ≅ freeOn (space K) 2 :=
  Iso.refl _

abbrev nativeMap := @NativeFramedPairBaseChange.bundleMap
  (space K) (model K M hM) (modelInclusion K M hM)
  (LagrangianArbitraryPlaneIncidence.planeSource K)
  (LagrangianArbitraryPlaneIncidence.planeSource_isFiniteLocallyFree K) (coefficientFrame K)

abbrev nativeSquare := @NativeFramedPairBaseChange.bundleSquare
  (space K) (model K M hM) (modelInclusion K M hM)
  (LagrangianArbitraryPlaneIncidence.planeSource K)
  (LagrangianArbitraryPlaneIncidence.planeSource_isFiniteLocallyFree K) (coefficientFrame K)

def quotientPullbackIso : bundle K (modelInclusion K M hM) ≅
    (Scheme.Modules.pullback (modelInclusion K M hM)).obj (quotientOnLG K).target :=
  Iso.refl ((Scheme.Modules.pullback (modelInclusion K M hM)).obj (quotientOnLG K).target)

def sections (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    Fin 2 → Γ(bundle K (modelInclusion K M hM),⊤) :=
  fun k => pullbackGlobalSections (modelInclusion K M hM) (quotientOnLG K).target
    (LagrangianArbitraryPlaneIncidence.originalSection K (s ∘ e) k)

def actualVectorIso :
    (Scheme.Modules.pullback (nativeMap K M hM)).obj (LagrangianArbitraryPlaneIncidence.quotientBundle K) ≅
      FreeTwoPairIncidence.pulledTarget (model K M hM) (bundle K (modelInclusion K M hM)) :=
  @NativeFramedPairBaseChange.vectorIso (space K) (model K M hM) (modelInclusion K M hM)
    (LagrangianArbitraryPlaneIncidence.planeSource K)
    (LagrangianArbitraryPlaneIncidence.planeSource_isFiniteLocallyFree K) (coefficientFrame K)
    (quotientOnLG K).target (bundle K (modelInclusion K M hM)) (quotientPullbackIso K M hM)

def actualLineIso :
    (Scheme.Modules.pullback (nativeMap K M hM)).obj (LagrangianArbitraryPlaneIncidence.lineBundle K) ≅
      tautologicalLine (model K M hM) :=
  @NativeFramedPairBaseChange.lineIso (space K) (model K M hM) (modelInclusion K M hM)
    (LagrangianArbitraryPlaneIncidence.planeSource K)
    (LagrangianArbitraryPlaneIncidence.planeSource_isFiniteLocallyFree K) (coefficientFrame K)

def actualEquationIso :
    (Scheme.Modules.pullback (nativeMap K M hM)).obj (LagrangianArbitraryPlaneIncidence.equationBundle K) ≅
      FreeTwoPairIncidence.equationBundle (model K M hM) (bundle K (modelInclusion K M hM)) :=
  TensorProductPullbackFrame.frame (nativeMap K M hM)
    (LagrangianArbitraryPlaneIncidence.quotientBundle K) (LagrangianArbitraryPlaneIncidence.lineBundle K)
    (FreeTwoPairIncidence.pulledTarget (model K M hM) (bundle K (modelInclusion K M hM)))
    (tautologicalLine (model K M hM)) (actualVectorIso K M hM) (actualLineIso K M hM)

theorem original_coordinate (k : Fin 2) :
    @NativeFramedPairBaseChange.coordinate (space K) (LagrangianArbitraryPlaneIncidence.planeSource K)
      (LagrangianArbitraryPlaneIncidence.planeSource_isFiniteLocallyFree K) (coefficientFrame K) k =
    LagrangianArbitraryPlaneIncidence.lineCoordinate K k := rfl

theorem actualVectorIso_apply (w : Fin 2 → (Fin 6 → K)) (k : Fin 2) :
    (actualVectorIso K M hM).hom.app ⊤
      (pullbackGlobalSections (nativeMap K M hM) (LagrangianArbitraryPlaneIncidence.quotientBundle K)
        (LagrangianArbitraryPlaneIncidence.quotientSection K w k)) =
    pullbackGlobalSections (projectiveBundleProjection (model K M hM)) (bundle K (modelInclusion K M hM))
      (pullbackGlobalSections (modelInclusion K M hM) (quotientOnLG K).target
        (LagrangianArbitraryPlaneIncidence.originalSection K w k)) :=
  @NativeFramedPairBaseChange.vectorIso_apply (space K) (model K M hM) (modelInclusion K M hM)
    (LagrangianArbitraryPlaneIncidence.planeSource K)
    (LagrangianArbitraryPlaneIncidence.planeSource_isFiniteLocallyFree K) (coefficientFrame K)
    (quotientOnLG K).target (bundle K (modelInclusion K M hM)) (quotientPullbackIso K M hM)
    (LagrangianArbitraryPlaneIncidence.originalSection K w k)

theorem actualLineIso_apply (k : Fin 2) :
    (actualLineIso K M hM).hom.app ⊤
      (pullbackGlobalSections (nativeMap K M hM) (LagrangianArbitraryPlaneIncidence.lineBundle K)
        (LagrangianArbitraryPlaneIncidence.lineCoordinate K k)) =
    tautCoordinate (model K M hM) k := by
  rw [← original_coordinate K k]
  exact @NativeFramedPairBaseChange.coordinate_apply (space K) (model K M hM) (modelInclusion K M hM)
    (LagrangianArbitraryPlaneIncidence.planeSource K)
    (LagrangianArbitraryPlaneIncidence.planeSource_isFiniteLocallyFree K) (coefficientFrame K) k

theorem actual_equationIso_apply (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    (actualEquationIso K M hM).hom.app ⊤
      (pullbackGlobalSections (nativeMap K M hM) (LagrangianArbitraryPlaneIncidence.equationBundle K)
        (LagrangianArbitraryPlaneIncidence.equationSection K (s ∘ e))) =
      FreeTwoPairIncidence.equationSection (model K M hM) (bundle K (modelInclusion K M hM))
        (sections K M hM s e) := by
  simp only [LagrangianArbitraryPlaneIncidence.equationSection,
    FreeTwoPairIncidence.equationSection,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := PairIncidencePullbackTerm.frame_pairing_apply (nativeMap K M hM)
    (LagrangianArbitraryPlaneIncidence.quotientBundle K) (LagrangianArbitraryPlaneIncidence.lineBundle K)
    (FreeTwoPairIncidence.pulledTarget (model K M hM) (bundle K (modelInclusion K M hM)))
    (tautologicalLine (model K M hM)) (actualVectorIso K M hM) (actualLineIso K M hM)
    (LagrangianArbitraryPlaneIncidence.quotientSection K (s ∘ e) k)
    (LagrangianArbitraryPlaneIncidence.lineCoordinate K k)
  rw [actualVectorIso_apply,actualLineIso_apply] at h
  exact h

theorem ideal_eq (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    FreeTwoPairIncidence.ideal (model K M hM) (bundle K (modelInclusion K M hM)) (sections K M hM s e) =
    (LagrangianArbitraryPlaneIncidence.incidenceIdeal K (s ∘ e)).comap (nativeMap K M hM) := by
  letI := bundle_rank K (modelInclusion K M hM)
  letI := LagrangianArbitraryPlaneIncidence.equationBundle_rank K
  letI := FreeTwoPairIncidence.equationBundle_rank (model K M hM) (bundle K (modelInclusion K M hM)) 3
  letI := isFiniteLocallyFreeOfRank_pullback (nativeMap K M hM)
    (LagrangianArbitraryPlaneIncidence.equationBundle K) 3
  have hi := LagrangianMatrixChart.sectionZeroIdeal_eq_of_iso 3 (actualEquationIso K M hM)
    (pullbackGlobalSections (nativeMap K M hM) (LagrangianArbitraryPlaneIncidence.equationBundle K)
      (LagrangianArbitraryPlaneIncidence.equationSection K (s ∘ e)))
  rw [actual_equationIso_apply K M hM s e] at hi
  exact hi.symm.trans (SectionZeroIdealFactorization.sectionZeroIdeal_pullback (nativeMap K M hM)
    (LagrangianArbitraryPlaneIncidence.equationBundle K) 3
    (LagrangianArbitraryPlaneIncidence.equationSection K (s ∘ e)))

def zeroIso (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    FreeTwoPairIncidence.space (model K M hM) (bundle K (modelInclusion K M hM)) (sections K M hM s e) ≅
      curveIncidence K M hM s e :=
  ClosedIdealPullbackPaste.zeroIsoPullback (LagrangianArbitraryPlaneIncidence.toLG K)
    (projectiveBundleProjection (model K M hM)) (nativeMap K M hM) (modelInclusion K M hM)
    (nativeSquare K M hM) (LagrangianArbitraryPlaneIncidence.incidenceIdeal K (s ∘ e))
    (FreeTwoPairIncidence.ideal (model K M hM) (bundle K (modelInclusion K M hM)) (sections K M hM s e))
    (ideal_eq K M hM s e)

@[reassoc]
theorem zeroIso_hom_fst (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    (zeroIso K M hM s e).hom ≫ pullback.fst _ _ =
      FreeTwoPairIncidence.toBase (model K M hM) (bundle K (modelInclusion K M hM)) (sections K M hM s e) :=
  ClosedIdealPullbackPaste.zeroIsoPullback_hom_fst (LagrangianArbitraryPlaneIncidence.toLG K)
    (projectiveBundleProjection (model K M hM)) (nativeMap K M hM) (modelInclusion K M hM)
    (nativeSquare K M hM) (LagrangianArbitraryPlaneIncidence.incidenceIdeal K (s ∘ e))
    (FreeTwoPairIncidence.ideal (model K M hM) (bundle K (modelInclusion K M hM)) (sections K M hM s e))
    (ideal_eq K M hM s e)

end M9Native.LagrangianIncidenceCurveBaseChange

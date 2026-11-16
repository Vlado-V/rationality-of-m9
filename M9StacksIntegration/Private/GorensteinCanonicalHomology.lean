module

public import M9StacksIntegration.CurveClosedPointDimension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineOfModuleCategory
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay

/-!
# Native Gorenstein canonical homology

Selected proof from pinned Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Curves/GenusCurve/DualizingDegree.lean. Source hash and namespace changes
are recorded in the audit. The theorem concerns an actual dualizing
complex with actual normalized derived stalks; the final smooth-curve
wrapper separately proves those inputs for its actual right adjoint.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

attribute [local instance high] HasDerivedCategory.standard

universe u

namespace M9Native.GorensteinCanonicalHomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Duality

/-- Gorenstein local rings make the actual degree −1 homology line
invertible when the actual dualizing stalks are normalized. -/
theorem homology_neg_one_isInvertible (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsGorenstein X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hstalk : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = 1)
    (ω : DerivedCategory X.Modules)
    (hω : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      Stacks.Duality.IsDualizingComplex ω)
    (hnorm : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      ∀ x : X, IsClosed ({x} : Set X) →
        Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor x).obj ω)) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((DerivedCategory.homologyFunctor X.Modules (-1)).obj ω) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  set M := (DerivedCategory.homologyFunctor X.Modules (-1)).obj ω with hM
  have hcoh : _root_.SheafOfModules.IsCoherent M := isCoherent_homology_neg_one f ω hω
  have hfp : M.IsFinitePresentation := isFinitePresentation_of_isCoherent M
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hlf : SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M 1 := by
    refine AffineOfModuleCategory.isFiniteLocallyFreeOfRank_of_closedPoint_stalks M hfp 1
      fun x hx => ?_
    have hA : Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) :=
      IsGorenstein.isGorensteinLocalRing x
    have hinv := (isGorensteinLocalRing_stalk_iff_isInvertible_derivedStalk ω hω x).mp hA
    obtain ⟨n, -, ⟨e⟩⟩ := (Dualizing.isInvertible_iff_homology_concentrated_free _).mp hinv
    have hCM : IsCohenMacaulayLocalRing (X.presheaf.stalk x) :=
      Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing _ hA
    have hnt : Nontrivial ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (X.presheaf.stalk x)) n).obj ((derivedStalkFunctor x).obj ω)) :=
      e.toLinearEquiv.toEquiv.nontrivial
    have hn : n = -1 := by
      by_contra hne
      by_cases h0 : n = 0
      · subst h0
        rcases (nontrivial_homology_zero_derivedStalk_iff f hdim ω x (hnorm x hx)).mp hnt with
          h | ⟨-, h⟩
        · rw [hstalk x hx] at h
          exact absurd h (by decide)
        · exact h hCM
      · have hz := isZero_homology_derivedStalk_of_ne f hdim ω x (hnorm x hx) hne h0
        exact (not_subsingleton _) (ModuleCat.subsingleton_of_isZero hz)
    subst hn
    let e₂ := ((((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryHomologyIso
      (-1)).app ω).symm ≪≫ e).toLinearEquiv
    exact ⟨AffineOfModuleCategory.stalkLinearEquivOverRingCatStalk M x
      (e₂.trans (Finsupp.uniqueLinearEquiv _ _ (default : ULift.{u} (Fin 1))).symm)⟩
  exact Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X M hlf

end M9Native.GorensteinCanonicalHomology

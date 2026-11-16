module

public import M9StacksIntegration.MukaiCanonicalBundleFromNet
public import M9StacksIntegration.MukaiEvaluationChoices
public import M9StacksIntegration.FieldPointMapRankConsequences

/-!
# Canonical generated semi-irreducible bundles under an actual module Iso

On the SAME original curve, the original sheaf isomorphism induces the
native K-linear cohomology equivalence. Its actual evaluation naturality
transports every independent tuple, so complete semi-irreducibility follows
from one side. Rank, genuine canonical top exterior and actual generators
are transported by the given isomorphism as well.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiCanonicalModuleIsoTransport

open MukaiSemiIrreducible

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The actual original-K complete-section map intertwines the literal
evaluation maps by postcomposition with the actual sheaf isomorphism. -/
theorem evaluation_iso {E F : X.Modules} (e : E ≅ F) {r : ℕ}
    (s : Fin r → cohomologyOverField k f E 0) :
    evaluation k f E s ≫ e.hom =
      evaluation k f F (fun i => MukaiEvaluationChoices.cohomologyEquiv k f e 0 (s i)) :=
  MukaiEvaluationChoices.evaluation_postcomp k f e.hom s

/-- Every independent complete-system tuple is transported through the
native cohomology map of the given Iso, with no supplied comparison. -/
theorem completeSemiIrreducible_of_iso {E F : X.Modules} (e : E ≅ F) (r : ℕ)
    (hE : CompleteSemiIrreducible k f E r) :
    CompleteSemiIrreducible k f F r := by
  intro t ht
  let H := MukaiEvaluationChoices.cohomologyEquiv k f e 0
  let s : Fin r → cohomologyOverField k f E 0 := fun i => H.symm (t i)
  have hs : LinearIndependent k s :=
    ht.map' H.symm.toLinearMap (LinearMap.ker_eq_bot.mpr H.symm.injective)
  have ht' : (fun i => H (s i)) = t := by
    funext i
    exact H.apply_symm_apply (t i)
  have hev := evaluation_iso k f e s
  change evaluation k f E s ≫ e.hom = evaluation k f F (fun i => H (s i)) at hev
  rw [ht'] at hev
  rcases hE s hs with hm | hr
  · left
    let := hm
    rw [← hev]
    infer_instance
  · right
    intro x
    rw [← hev]
    have h := FieldPointMapRankConsequences.mapRankAt_iso_conjugate
      (evaluation k f E s) (Iso.refl _) e x
    simpa only [Iso.refl_hom, Category.id_comp] using h.trans (hr x)

theorem completeSemiIrreducible_iff {E F : X.Modules} (e : E ≅ F) (r : ℕ) :
    CompleteSemiIrreducible k f E r ↔ CompleteSemiIrreducible k f F r :=
  ⟨completeSemiIrreducible_of_iso k f e r,
    completeSemiIrreducible_of_iso k f e.symm r⟩

/-- The original generator sections are mapped by the original module
isomorphism, yielding genuine generating sections of its target. -/
theorem globallyGenerated_of_iso {E F : X.Modules} (e : E ≅ F)
    (hE : GloballyGenerated E) : GloballyGenerated F := by
  obtain ⟨G⟩ := hE
  exact ⟨G.ofEpi e.hom⟩

theorem globallyGenerated_iff {E F : X.Modules} (e : E ≅ F) :
    GloballyGenerated E ↔ GloballyGenerated F :=
  ⟨globallyGenerated_of_iso e, globallyGenerated_of_iso e.symm⟩

variable [IsProper f]

/-- All five actual canonical generated semi-irreducible properties
follow on the target from ONE side of the original module isomorphism. -/
theorem isCanonicalGeneratedSemi_of_iso {E F : X.Modules} (e : E ≅ F)
    (hE : MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f E) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f F := by
  obtain ⟨hr, h6, ⟨d⟩, hgen, hsemi⟩ := hE
  refine ⟨SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e hr, ?_, ?_, ?_, ?_⟩
  · exact (MukaiEvaluationChoices.cohomologyEquiv k f e 0).finrank_eq.symm.trans h6
  · exact ⟨((Scheme.Modules.exteriorPowerFunctor X (3 : ℤ)).mapIso e.symm) ≪≫ d⟩
  · exact globallyGenerated_of_iso e hgen
  · exact completeSemiIrreducible_of_iso k f e 3 hsemi

/-- The full predicate depends only on the actual isomorphism class of
the module on the SAME original curve, with its original field action. -/
theorem isCanonicalGeneratedSemi_iff {E F : X.Modules} (e : E ≅ F) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f E ↔
      MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f F :=
  ⟨isCanonicalGeneratedSemi_of_iso k f e,
    isCanonicalGeneratedSemi_of_iso k f e.symm⟩

end M9Native.MukaiCanonicalModuleIsoTransport

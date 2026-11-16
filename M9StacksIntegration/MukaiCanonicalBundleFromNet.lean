module

public import M9StacksIntegration.MukaiBundleFromNet
public import M9StacksIntegration.MukaiBundleRecognition
public import M9StacksIntegration.MukaiResidualBundleUniqueness

/-!
# Existence and uniqueness of the actual canonical Mukai bundle

The bundle property refers to the original native sheaf, its complete
cohomology space and the full semi-irreducibility predicate. Recognition
constructs the actual residual-net extensions for any two such bundles;
the proved extension comparison then gives an actual sheaf isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiCanonicalBundleFromNet

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The original rank-three canonical bundle with its complete six
sections, actual generation and full complete semi-irreducibility. -/
def IsCanonicalGeneratedSemi (E : X.Modules) : Prop :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3 ∧
  Module.finrank k (cohomologyOverField k f E 0) = 6 ∧
  Nonempty (Scheme.Modules.exteriorPower E 3 ≅ Stacks.Duality.dualizingSheafOverField f) ∧
  MukaiSemiIrreducible.GloballyGenerated E ∧
  MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3

/-- Every two actual canonical Mukai bundles are isomorphic, by
recognizing both as genuine extensions of the same original nets. -/
theorem canonical_generated_semi_bundles_iso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A B : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f A.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f B.L 0))
    (hres : tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f)
    (E F : X.Modules)
    (hE : IsCanonicalGeneratedSemi f E)
    (hF : IsCanonicalGeneratedSemi f F) : Nonempty (E ≅ F) := by
  obtain ⟨hrE, h6E, ⟨dE⟩, hgenE, hsemiE⟩ := hE
  obtain ⟨hrF, h6F, ⟨dF⟩, hgenF, hsemiF⟩ := hF
  let := hrE
  let := hrF
  obtain ⟨i, p, w, hS, hgamma, hn⟩ :=
    MukaiBundleRecognition.exists_nonsplit_gammaSplit_extension_of_semi k f
      hg hnp A B bA bB E h6E hgenE hsemiE dE hres
  obtain ⟨i', p', w', hS', hgamma', hn'⟩ :=
    MukaiBundleRecognition.exists_nonsplit_gammaSplit_extension_of_semi k f
      hg hnp A B bA bB F h6F hgenF hsemiF dF hres
  exact MukaiResidualBundleUniqueness.gammaSplit_middle_iso_complete_nets f
    hg hnp A B bA bB hres hS hS' hgamma hgamma' hn hn'

section FromOneNet

variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
  (Stacks.Duality.dualizingSheafOverField f)]

/-- One original degree-eight net constructs the actual canonical Mukai
bundle, unique up to an actual O-linear isomorphism among all bundles
with the stated genuine complete-system properties. -/
theorem exists_unique_up_to_iso_from_net
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2) :
    ∃ E : X.Modules, IsCanonicalGeneratedSemi f E ∧
      ∀ F : X.Modules, IsCanonicalGeneratedSemi f F → Nonempty (E ≅ F) := by
  let B := MukaiResidualNet.residualNet f (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A
  let bA := MukaiLemmaFiveOne.completeNetBasis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A
  let bB := MukaiResidualNet.residualNetBasis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A
  let hres : tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f :=
    MukaiResidualNet.residualNetTensorIso f
      (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A
  obtain ⟨E, hr, h6, hd, _, hgen, hsemi⟩ :=
    MukaiBundleFromNet.exists_canonical_generated_semiIrreducible_from_net f hg hnp A
  have hE : IsCanonicalGeneratedSemi f E := ⟨hr, h6, hd, hgen, hsemi⟩
  refine ⟨E, hE, ?_⟩
  intro F hF
  exact canonical_generated_semi_bundles_iso f hg hnp A B bA bB hres E F hE hF

/-- The Brill--Noether existence input is solely the existence of the
original degree-eight net, with no residual net, basis or bundle choice. -/
theorem exists_unique_up_to_iso_of_net_exists
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (hnet : Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)) :
    ∃ E : X.Modules, IsCanonicalGeneratedSemi f E ∧
      ∀ F : X.Modules, IsCanonicalGeneratedSemi f F → Nonempty (E ≅ F) := by
  obtain ⟨A⟩ := hnet
  exact exists_unique_up_to_iso_from_net f hg hnp A

end FromOneNet

end M9Native.MukaiCanonicalBundleFromNet

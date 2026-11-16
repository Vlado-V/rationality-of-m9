module

public import M9StacksIntegration.MukaiResidualBundleExistence
public import M9StacksIntegration.MukaiResidualNet

/-!
# The actual Mukai bundle from one original degree-eight net

The second net, its complete section basis and its residual isomorphism
are constructed from the original net. The canonical-line instance here
is the genuine smooth-curve property supplied by the separate native
dualizing-sheaf construction; no rank-three bundle supplies that input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiBundleFromNet

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
  (Stacks.Duality.dualizingSheafOverField f)]

/-- One actual degree-eight net suffices: its literal residual net and
all complete bases are constructed, then the actual canonical rank-three
bundle is produced with both native determinant conventions. -/
theorem exists_canonical_generated_semiIrreducible_from_net
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2) :
    ∃ E : X.Modules,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3 ∧
      Module.finrank k (cohomologyOverField k f E 0) = 6 ∧
      Nonempty (Scheme.Modules.exteriorPower E 3 ≅ Stacks.Duality.dualizingSheafOverField f) ∧
      Nonempty (Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f) ∧
      MukaiSemiIrreducible.GloballyGenerated E ∧
      MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3 := by
  let B := MukaiResidualNet.residualNet f (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A
  let bA := MukaiLemmaFiveOne.completeNetBasis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A
  let bB := MukaiResidualNet.residualNetBasis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A
  obtain ⟨E, hr, h6, ⟨d⟩, hgen, hsemi⟩ :=
    MukaiResidualBundleExistence.exists_canonical_generated_semiIrreducible_complete_nets f
      hg hnp A B bA bB
      (MukaiResidualNet.residualNetTensorIso f
        (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A)
  letI := hr
  let d' : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f :=
    (Scheme.Modules.exteriorPowerIsoDeterminant E 3).symm ≪≫ d
  exact ⟨E, hr, h6, ⟨d⟩, ⟨d'⟩, hgen, hsemi⟩

/-- The geometric input may be the existence of the original native
net; no particular residual net or section tuple is an additional input. -/
theorem exists_canonical_generated_semiIrreducible_of_net_exists
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (hnet : Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)) :
    ∃ E : X.Modules,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3 ∧
      Module.finrank k (cohomologyOverField k f E 0) = 6 ∧
      Nonempty (Scheme.Modules.exteriorPower E 3 ≅ Stacks.Duality.dualizingSheafOverField f) ∧
      Nonempty (Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f) ∧
      MukaiSemiIrreducible.GloballyGenerated E ∧
      MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3 := by
  obtain ⟨A⟩ := hnet
  exact exists_canonical_generated_semiIrreducible_from_net f hg hnp A

end M9Native.MukaiBundleFromNet

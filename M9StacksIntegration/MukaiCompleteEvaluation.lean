module

public import M9StacksIntegration.CompleteEvaluationGeneration
public import M9StacksIntegration.MinimalDegreeSeriesGeneration

/-!
# The original complete net and pencil evaluations generate

The native minimal-degree theorem generates the original chosen linear
series. The checked complete-evaluation factorization then gives
epimorphy for any actual complete cohomology basis, without identifying
the two native cohomology-to-sections comparisons.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.MukaiCompleteEvaluation

open CategoryTheory AlgebraicGeometry
open MukaiBundle MukaiDualSpanSections

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- Excluding the lower-degree nets generates the original complete
degree-eight evaluation, for every chosen complete cohomology basis. -/
theorem degree_eight_completeNetEvaluation_epi
    (hno7 : ∀ d : ℕ, d ≤ 7 → ¬ Nonempty (LinearSeries k f hdim d 2))
    (E : LinearSeries k f hdim 8 2)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f E.L 0)) :
    Epi (netEvaluation E.L (completeNetSections f E.L b)) := by
  let := E.isInvertible
  let : Module.Finite k E.V := Module.finite_of_finrank_pos (by rw [E.finrank_eq]; decide)
  let bE : Module.Basis (Fin 3) k E.V := Module.finBasisOfFinrankEq k E.V E.finrank_eq
  let t : ULift.{u} (Fin 3) → Γ(E.L, ⊤) :=
    fun i => Stacks.LinearSeriesMorphism.seriesSections E bE i.down
  have ht : Stacks.ProjectiveFromSections.GeneratesStalks t :=
    CompleteEvaluationGeneration.generatesStalks_ulift E.L _
      (MinimalDegreeSeriesGeneration.degree_eight_net_generates f hdim hno7 E bE)
  exact CompleteEvaluationGeneration.completeNetEvaluation_epi_of_generatesStalks f E.L b t ht

/-- On the nonpentagonal curve the original degree-six pencil gives
epimorphic evaluation of every actual complete two-element basis. -/
theorem degree_six_completePencilEvaluation_epi [IsAlgClosed k]
    (hno5 : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 6 1)
    (b : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f E.L 0)) :
    Epi (CompleteEvaluationGeneration.basisEvaluation f E.L b) := by
  let := E.isInvertible
  let : Module.Finite k E.V := Module.finite_of_finrank_pos (by rw [E.finrank_eq]; decide)
  let bE : Module.Basis (Fin 2) k E.V := Module.finBasisOfFinrankEq k E.V E.finrank_eq
  let t : ULift.{u} (Fin 2) → Γ(E.L, ⊤) :=
    fun i => Stacks.LinearSeriesMorphism.seriesSections E bE i.down
  have ht : Stacks.ProjectiveFromSections.GeneratesStalks t :=
    CompleteEvaluationGeneration.generatesStalks_ulift E.L _
      (MinimalDegreeSeriesGeneration.degree_six_pencil_generates f hdim hno5 E bE)
  exact CompleteEvaluationGeneration.basisEvaluation_epi_of_generatesStalks f E.L b t ht

end M9Native.MukaiCompleteEvaluation

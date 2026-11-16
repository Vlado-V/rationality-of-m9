module

public import M9StacksIntegration.MukaiPointTwistBounds
public import M9StacksIntegration.MinimalDegreeSeriesGeneration
public import M9StacksIntegration.CompleteEvaluationGeneration
public import M9StacksIntegration.MukaiPencilQuotient

/-! An arbitrary original degree-five pencil is complete and generated
when there is no original degree-four pencil. Actual effective-divisor
addition excludes all smaller pencils. Genuine point removal then bounds
complete H0, and native minimal degree generates the original basis.
No complete-section count or basepoint-free pair is supplied. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module
open Stacks.LinearSeriesMorphism Stacks.ProjectiveFromSections

universe u

namespace M9Native.DegreeFivePencilNormalization

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1)

/-- Actual addition of an effective divisor promotes every smaller
pencil to degree four, so the original no-four theorem excludes it. -/
theorem no_smaller_pencil
    (hno4 : ¬ Nonempty (LinearSeries K f hdim 4 1)) :
    ∀ d : ℕ, d < 5 → ¬ Nonempty (LinearSeries K f hdim d 1) := by
  intro d hd hp
  exact hno4
    (M9StacksIntegration.LinearSeriesAddEffectiveDivisor.nonempty_linearSeries_of_degree_le
      f hdim hp (by omega))

/-- If a degree-five pencil had a third complete section, actual point
removal would leave two sections in strictly smaller degree. -/
theorem h0_eq_two
    (hno4 : ¬ Nonempty (LinearSeries K f hdim 4 1))
    (A : LinearSeries K f hdim 5 1) :
    finrank K (cohomologyOverField K f A.L 0) = 2 := by
  let := A.isInvertible
  let := CurveDivisorSections.invertible_cohomology_zero_finite f A.L
  have hlow : 2 ≤ finrank K (cohomologyOverField K f A.L 0) := by
    have hV := Submodule.finrank_le A.V
    rw [A.finrank_eq] at hV
    exact hV
  have hupp : finrank K (cohomologyOverField K f A.L 0) ≤ 2 := by
    by_contra hgt
    obtain ⟨L', hL', hdeg', hdrop⟩ :=
      MukaiTwistBounds.exists_lower_degree_one_less_H0 f hdim A.L (by omega)
    let := hL'
    have hmin := MinimalDegreeSeriesGeneration.degree_lower_bound_of_no_smaller_series
      f hdim 5 1 (no_smaller_pencil f hdim hno4) L' (by omega)
    have hA := A.degree_eq
    omega
  exact le_antisymm hupp hlow

/-- The original two basis sections generate the original line itself;
the native equality case constructs the isomorphism from its actual span. -/
theorem generatesStalks
    (hno4 : ¬ Nonempty (LinearSeries K f hdim 4 1))
    (A : LinearSeries K f hdim 5 1) (b : Module.Basis (Fin 2) K A.V) :
    GeneratesStalks (seriesSections A b) := by
  apply MinimalDegreeSeriesGeneration.generatesStalks_of_minimal_degree
    f hdim (isRegular_of_smooth_over_field f) A b
  intro L hL h0
  let := hL
  exact MinimalDegreeSeriesGeneration.degree_lower_bound_of_no_smaller_series
    f hdim 5 1 (no_smaller_pencil f hdim hno4) L h0

/-- Produce an actual generating pair in the compatible-section
spelling of the genuine free-five contradiction, together with complete
H0 dimension two. Neither of those conclusions is a premise. -/
theorem exists_generating_pair
    (hno4 : ¬ Nonempty (LinearSeries K f hdim 4 1))
    (A : LinearSeries K f hdim 5 1) :
    ∃ t : ULift.{u} (Fin 2) → A.L.sections,
      finrank K (cohomologyOverField K f A.L 0) = 2 ∧
      Epi (MukaiPencilQuotient.pencilEvaluation A.L t) := by
  let := A.isInvertible
  let : Module.Finite K A.V := Module.finite_of_finrank_pos
    (by rw [A.finrank_eq]; decide)
  let b : Module.Basis (Fin 2) K A.V := Module.finBasisOfFinrankEq K A.V A.finrank_eq
  let q : ULift.{u} (Fin 2) → Γ(A.L, ⊤) :=
    fun i => seriesSections A b i.down
  have hq : GeneratesStalks q :=
    CompleteEvaluationGeneration.generatesStalks_ulift A.L _
      (generatesStalks f hdim hno4 A b)
  let t : ULift.{u} (Fin 2) → A.L.sections :=
    fun i => (Stacks.NonvanishingSpelling.sectionsEquiv X A.L).symm (q i)
  refine ⟨t, h0_eq_two f hdim hno4 A, ?_⟩
  change Epi (A.L.freeHomEquiv.symm t)
  exact CompleteEvaluationGeneration.freeEvaluation_epi_of_generatesStalks A.L q hq

end M9Native.DegreeFivePencilNormalization

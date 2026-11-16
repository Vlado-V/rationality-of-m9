module

public import M9StacksIntegration.MukaiRankTwoCriterion
public import M9StacksIntegration.MukaiSaturationRank

/-!
# The actual saturated line furnished by the four-section criterion

The independent pair is produced by the genuine native exterior
evaluation map. The line is the prescribed saturation of this very
pair's evaluation image, constructed as a kernel of the torsion-free
quotient of its cokernel. Its invertibility and its two independent
sections are conclusions, with no subline or generic-rank premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiRankTwoSaturatedLine

variable (k : Type u) [Field k] [IsAlgClosed k]
variable {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) (F : X.Modules)
variable [SheafOfModules.IsFiniteLocallyFree.{u,u,u} F]
variable [FiniteDimensional k (cohomologyOverField k f F 0)]
variable [FiniteDimensional k
  (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0)]

/-- Mukai's four-section rank-two wedge criterion produces an actual
saturated invertible subsheaf with at least two sections. -/
theorem exists_pair_with_saturated_line
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hsections : 4 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 4) :
    ∃ s : Fin 2 → cohomologyOverField k f F 0,
      LinearIndependent k s ∧
        ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 s) = 0 ∧
          (letI : F.IsQuasicoherent :=
            Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
           letI : (cokernel (MukaiSemiIrreducible.evaluation k f F s)).IsQuasicoherent :=
            MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f F s
           SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
               (MukaiEvaluationSaturation.saturation
                 (MukaiSemiIrreducible.evaluation k f F s)) ∧
             2 ≤ Module.finrank k (cohomologyOverField k f
               (MukaiEvaluationSaturation.saturation
                 (MukaiSemiIrreducible.evaluation k f F s)) 0)) := by
  obtain ⟨a,b,hab,hw⟩ :=
    MukaiRankTwoCriterion.exists_two_sections_zero_exteriorEvaluation k f F hsections hdet
  exact ⟨![a,b],hab,hw,
    MukaiSaturationRank.actual_pair_saturation_line_with_two_sections
      k f F ![a,b] hreg hdim hab hw⟩

end M9Native.MukaiRankTwoSaturatedLine

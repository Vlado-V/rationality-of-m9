module

public import M9StacksIntegration.LagrangianChowPolynomials
public import M9StacksIntegration.LagrangianFlagPowerStages
public import M9StacksIntegration.ChowLineFamilyComparison

/-!
# Actual polynomial evaluation preserves the original flag-line isomorphisms

The positive projective lines are compared to the original three native
quotient-flag lines by the proved sheaf isomorphisms. Equality of every
integer polynomial operator follows from genuine line-cap invariance.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianPolynomialLineCongruence
open ChowCapWords GradedLineCapSubring LagrangianChowPolynomials

theorem evaluate_congr (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    (L M : Fin 3 → InvertibleLine Y) (e : ∀ i, (L i).1 ≅ (M i).1) :
    evaluate C q L = evaluate C q M := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [evaluate_C, evaluate_C]
  · intro i
    rw [evaluate_X, evaluate_X]
    exact ChowLineFamilyComparison.lineFamily_congr C q (L i) (M i) (e i)

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1LFT LagrangianFlagPowerStages.projection2LFT
  LagrangianFlagPowerStages.projection3LFT

variable {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]

local instance originalLine1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.line1 E) 1 := FlagThreeQuotient.line1_rank E
local instance originalLine2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.line2 E) 1 := FlagThreeQuotient.line2_rank E
local instance originalLine3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (FlagThreeQuotient.line3 E) 1 := FlagThreeQuotient.line3_rank E

/-- The ORIGINAL three native flag lines, in the original order. -/
def originalLines : Fin 3 → InvertibleLine (LagrangianFlagPowerStages.space3 E) :=
  ![⟨FlagThreeQuotient.line1 E, GenuineChern.isInvertible_of_rank_one _⟩,
    ⟨FlagThreeQuotient.line2 E, GenuineChern.isInvertible_of_rank_one _⟩,
    ⟨FlagThreeQuotient.line3 E, GenuineChern.isInvertible_of_rank_one _⟩]

def positive_original_iso (i : Fin 3) :
    (LagrangianFlagPowerStages.positiveLines E i).1 ≅ (originalLines E i).1 := by
  exact Fin.cases (LagrangianFlagPowerStages.first_original_iso E)
    (fun j => Fin.cases (LagrangianFlagPowerStages.second_original_iso E)
      (fun k => Fin.cases (LagrangianFlagPowerStages.third_original_iso E)
        (fun l => Fin.elim0 l) k) j) i

/-- This is an equality of the actual original operational ring maps,
not a numerical root-realization hypothesis. -/
theorem evaluate_positive_eq_original (C : ChowSituation.{u})
    (q : X ⟶ C.S) [LocallyOfFiniteType q] :
    evaluate C (LagrangianFlagPowerStages.baseMap3 E C q)
        (LagrangianFlagPowerStages.positiveLines E) =
      evaluate C (LagrangianFlagPowerStages.baseMap3 E C q) (originalLines E) :=
  evaluate_congr C (LagrangianFlagPowerStages.baseMap3 E C q)
    (LagrangianFlagPowerStages.positiveLines E) (originalLines E) (positive_original_iso E)

end M9Native.LagrangianPolynomialLineCongruence

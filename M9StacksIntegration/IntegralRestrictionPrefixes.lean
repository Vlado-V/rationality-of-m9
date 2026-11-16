module

public import M9StacksIntegration.IntegralRestrictionLadder
public import Mathlib.Data.List.OfFn

/-! List-prefix geometry builds the literal recursive integral-cut
predicate.  The data are actual prefix integrality and actual nonzero
restricted sections, with no restriction-kernel condition. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open Stacks.Bertini

universe u

namespace M9Native.IntegralRestrictionPrefixes

open IntegralRestrictionLadder IteratedLineSectionCuts

variable (D : FamilyDivisors.{u,u})

abbrev prefixCut (vs : List D.V) (A : Over D.X) (i : ℕ) : Over D.X :=
  iteratedCut D.L ((vs.take i).map D.sectionOf) A

theorem integralSteps_of_prefixes (vs : List D.V) (A : Over D.X)
    (hI : ∀ (i : ℕ) (_hi : i < vs.length), IsIntegral (prefixCut D vs A i).left)
    (hN : ∀ (i : ℕ) (hi : i < vs.length),
      (D.pullbackAlong (prefixCut D vs A i).hom).sectionOf vs[i] ≠ 0) :
    IntegralSteps D vs A := by
  induction vs generalizing A with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨hI 0 (by simp),hN 0 (by simp),?_⟩
    exact ih (cut D.L A (D.sectionOf v))
      (fun i hi => hI (i+1) (Nat.succ_lt_succ hi))
      (fun i hi => hN (i+1) (Nat.succ_lt_succ hi))

theorem integralSteps_of_simultaneous_prefixes (vs : List D.V)
    (hI : ∀ (i : ℕ) (_hi : i < vs.length),
      IsIntegral (simultaneousCut D.L ((vs.take i).map D.sectionOf)).left)
    (hN : ∀ (i : ℕ) (hi : i < vs.length),
      (D.pullbackAlong (simultaneousCut D.L ((vs.take i).map D.sectionOf)).hom).sectionOf vs[i] ≠ 0) :
    IntegralSteps D vs (Over.mk (𝟙 D.X)) :=
  integralSteps_of_prefixes D vs (Over.mk (𝟙 D.X)) hI hN

end M9Native.IntegralRestrictionPrefixes
end

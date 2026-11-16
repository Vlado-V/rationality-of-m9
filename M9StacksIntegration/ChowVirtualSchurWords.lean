module

public import M9StacksIntegration.ChowVirtualComponentCommutation
public import M9StacksIntegration.Private.CommutingSchurWords

/-!
# The actual natural six-word operator is the actual Schur operator

The components are those of the original genuine virtual Chern family.
Their pairwise commutation is proved internally from native geometric
Chern-component commutation and finite inverse recurrence. The pure
arbitrary-ring word identity then gives the literal Schur order.
No Pairwise or ambient commutativity input, and no geometric
pushforward identity, is supplied here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.ChowVirtualSchurWords
open AlgebraicGeometry CategoryTheory Stacks.Chow
open M9Native.GradedCapVirtualSchur M9Native.ChowVirtualComponentCommutation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q]

/-- The natural ordered six-word expression equals the literal actual
Schur operator. All needed component commutations are derived from the
original finite locally free modules; none are premises. -/
theorem ordered_words_eq_schur333 (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] :
    let v := virtualFamily C q F E rF rE
    homComponent 3 v * homComponent 3 v * homComponent 3 v -
      homComponent 3 v * homComponent 2 v * homComponent 4 v -
      homComponent 2 v * homComponent 4 v * homComponent 3 v +
      homComponent 2 v * homComponent 2 v * homComponent 5 v +
      homComponent 1 v * homComponent 4 v * homComponent 4 v -
      homComponent 1 v * homComponent 3 v * homComponent 5 v = schur333 v := by
  let v := virtualFamily C q F E rF rE
  have hc (i j : ℕ) : Commute (homComponent i v) (homComponent j v) :=
    commute_homComponent_virtualFamily C q F E rF rE i j
  simpa only [schur333] using CommutingSchurWords.schur_words_of_commute
    (homComponent 1 v) (homComponent 2 v) (homComponent 3 v)
    (homComponent 4 v) (homComponent 5 v)
    (hc 1 4) (hc 2 4) (hc 2 5) (hc 1 3) (hc 1 5) (hc 3 5)

end M9Native.ChowVirtualSchurWords

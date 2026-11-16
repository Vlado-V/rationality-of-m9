module

public import M9StacksIntegration.DirectC9F10Chern
public import M9StacksIntegration.DirectC9UnitTwistRows
public import M9StacksIntegration.ChowChernUnitRows

/-!
# The actual BN virtual Chern family after genuine unit-jet removal

The actual eight fixed-point quotient-unit rows identify the actual
total Chern families of E18 and E10. Their genuine recursive inverse
families therefore agree. The actual F10 subline filtration proves its
Chern family is one, so the literal original virtual family is the
inverse family of the original E18. No K-zero realization, splitting,
root product, inverse compatibility, or Chern formula is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.CurvePower
open Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.DirectC9VirtualChern

open DirectC9Bundles (E10 E18 F10 twistPushforward)
open GradedCapVirtualSchur

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom] (c₀ : power C 0 ⟶ C)
  (hg : genus C.hom = 9)
  (A : ChowSituation.{u}) (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s]

/-- The genuine native Chern family of each retained large twist,
using its already-proved actual ordinary bundle rank. -/
def twistChernFamily (q : ℕ) (hq : 8 ≤ q) : GradedCapFamily (chowGroup A s) :=
  @chernFamily A (power C 9).left s _ (twistPushforward k C c₀ q) (q + 1)
    (DirectC9Bundles.twistPushforward_rank k C c₀ hg q hq)

/-- One actual quotient-unit geometric row removes one fixed jet. -/
theorem twistChernFamily_succ (q : ℕ) (hq : 8 ≤ q) :
    twistChernFamily k C c₀ hg A s (q + 1) (hq.trans (Nat.le_succ q)) =
      twistChernFamily k C c₀ hg A s q hq := by
  unfold twistChernFamily
  obtain ⟨i,p,w,h⟩ := DirectC9UnitTwistRows.exists_unitTwistRow k C c₀ hg q hq
  exact @ChowChernUnitRows.chernFamily_eq A (power C 9).left s _
    (ShortComplex.mk i p w) h (Iso.refl _) (q + 1)
    (DirectC9Bundles.twistPushforward_rank k C c₀ hg q hq)
    (DirectC9Bundles.twistPushforward_rank k C c₀ hg (q + 1) (hq.trans (Nat.le_succ q)))

/-- Iterating actual unit-quotient rows preserves the actual Chern
family. The iteration composes the proved one-row equalities. -/
theorem twistChernFamily_add (q : ℕ) (hq : 8 ≤ q) (n : ℕ) :
    twistChernFamily k C c₀ hg A s (q + n) (hq.trans (Nat.le_add_right q n)) =
      twistChernFamily k C c₀ hg A s q hq := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (twistChernFamily_succ k C c₀ hg A s (q + n)
        (hq.trans (Nat.le_add_right q n))).trans ih

/-- The actual quotient-unit jet tower removes all eight fixed jets,
in its genuine E10-to-E18 geometric orientation. -/
theorem E18_chernFamily_eq_E10 :
    @chernFamily A (power C 9).left s _ (E18 k C c₀) 18
      (DirectC9Bundles.E18_rank k C c₀ hg) =
    @chernFamily A (power C 9).left s _ (E10 k C c₀) 10
      (DirectC9Bundles.E10_rank k C c₀ hg) :=
  twistChernFamily_add k C c₀ hg A s 9 (Nat.le_succ 8) 8

/-- The genuine native recursive inverse is unchanged by the actual
eight quotient-unit rows; no inverse-compatibility premise is used. -/
theorem inverse_E10_eq_E18 :
    @inverseFamily A (power C 9).left s _ (E10 k C c₀) 10
      (DirectC9Bundles.E10_rank k C c₀ hg) =
    @inverseFamily A (power C 9).left s _ (E18 k C c₀) 18
      (DirectC9Bundles.E18_rank k C c₀ hg) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E10 k C c₀) 10 :=
    DirectC9Bundles.E10_rank k C c₀ hg
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E18 k C c₀) 18 :=
    DirectC9Bundles.E18_rank k C c₀ hg
  rw [inverseFamily_eq_gradedRightInv, inverseFamily_eq_gradedRightInv,
    E18_chernFamily_eq_E10 k C c₀ hg A s]

/-- The literal original virtual operator c(F10)c(E10)^(-1) is the
actual inverse Chern family of E18, by genuine geometric jet rows. -/
theorem virtualF10_E10_eq_inverseE18 :
    @virtualFamily A (power C 9).left s _ (F10 k C c₀) (E10 k C c₀) 10 10
      (DirectC9Bundles.F10_rank k C c₀) (DirectC9Bundles.E10_rank k C c₀ hg) =
    @inverseFamily A (power C 9).left s _ (E18 k C c₀) 18
      (DirectC9Bundles.E18_rank k C c₀ hg) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (F10 k C c₀) 10 :=
    DirectC9Bundles.F10_rank k C c₀
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E10 k C c₀) 10 :=
    DirectC9Bundles.E10_rank k C c₀ hg
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E18 k C c₀) 18 :=
    DirectC9Bundles.E18_rank k C c₀ hg
  rw [virtualFamily, DirectC9F10Chern.F10_chernFamily_eq_one, one_mul,
    inverse_E10_eq_E18 k C c₀ hg A s]

end M9Native.DirectC9VirtualChern

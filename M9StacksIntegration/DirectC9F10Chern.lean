module

public import M9StacksIntegration.DirectC9FJetRows
public import M9StacksIntegration.ChowChernUnitSubrows

/-!
# The actual integral Chow Chern family of the original F10 is one

The original ordinary restriction bundles have the actual successive
unit SUBLINE rows proved from the Cartier sum sequence. Starting from
the genuine first-jet/unit isomorphism, native Whitney removes one
actual unit subline at each step. Thus the literal actual rank-ten
bundle has Chern family one on every original integral Chow group.
No K-zero realization, chosen splitting, or Chern identity is assumed.
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

namespace M9Native.DirectC9F10Chern

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom] (c₀ : power C 0 ⟶ C)
  (A : ChowSituation.{u}) (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s]

/-- Every original fixed-section restriction image has actual Chern
family one, by its actual unit-subline restriction rows. -/
theorem restriction_chernFamily_eq_one (q : ℕ) :
    @chernFamily A (power C 9).left s _
      (DirectC9Bundles.restrictionPushforward k C c₀ q) (q + 1)
      (DirectC9Bundles.restrictionPushforward_rank k C c₀ q) = 1 := by
  induction q with
  | zero =>
      let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
          (DirectC9Bundles.restrictionPushforward k C c₀ 0) 1 :=
        DirectC9Bundles.restrictionPushforward_rank k C c₀ 0
      exact chernFamily_eq_one_of_iso_unit A s _
        (DirectC9JetLines.nonempty_firstJet_iso_unit k C c₀).some
  | succ q ih =>
      obtain ⟨i,p,w,h⟩ := DirectC9FJetRows.exists_unitSubrow k C c₀ q
      let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
          (DirectC9Bundles.restrictionPushforward k C c₀ q) (q + 1) :=
        DirectC9Bundles.restrictionPushforward_rank k C c₀ q
      let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
          (DirectC9Bundles.restrictionPushforward k C c₀ (q + 1)) ((q + 1) + 1) :=
        DirectC9Bundles.restrictionPushforward_rank k C c₀ (q + 1)
      have hrow := ChowChernUnitSubrows.chernFamily_eq A s
        (ShortComplex.mk i p w) h (Iso.refl _) (q + 1)
      exact hrow.trans ih

/-- The retained actual rank-ten F10, with the retained ordinary
pushforward spelling, has genuine integral Chow Chern family one. -/
theorem F10_chernFamily_eq_one :
    @chernFamily A (power C 9).left s _ (DirectC9Bundles.F10 k C c₀) 10
      (DirectC9Bundles.F10_rank k C c₀) = 1 :=
  restriction_chernFamily_eq_one k C c₀ A s 9

end M9Native.DirectC9F10Chern

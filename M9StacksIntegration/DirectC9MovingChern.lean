module

public import M9StacksIntegration.DirectC9MovingRows
public import M9StacksIntegration.DirectC9GraphRootEvaluation
public import M9StacksIntegration.ChowWhitneyLineTower

/-!
# The actual E18 Whitney product of the original moving-graph lines

The nine actual ordinary bundle short exact rows and their proved
ranks give the literal integral Chow Chern product. Its order is the
actual initial rank-nine bundle on the left, then the original
quotient lines in chronological order. No product, K-zero realization,
root formula, or Chern identity is a hypothesis.
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

namespace M9Native.DirectC9MovingChern

open DirectC9Bundles (movingPushforward)
open GradedLineCapSubring (lineFamily)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom] (c₀ : power C 0 ⟶ C)
  (hg : genus C.hom = 9)
  (A : ChowSituation.{u}) (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

/-- The true raw product is initial bundle first and κ0 through κ8
afterwards; it is obtained from the actual nine quotient rows. -/
theorem moving_chernFamily_eq_product :
    @chernFamily A (power C 9).left s _ (movingPushforward k C c₀ 9 (Nat.le_refl 9)) 18
      (by simpa using DirectC9Bundles.movingPushforward_rank k C c₀ hg 9 (Nat.le_refl 9)) =
    @chernFamily A (power C 9).left s _ (movingPushforward k C c₀ 0 (Nat.zero_le 9)) 9
      (by simpa using DirectC9Bundles.movingPushforward_rank k C c₀ hg 0 (Nat.zero_le 9)) *
      ChowWhitneyLineTower.orderedPrefix
        (fun a : Fin 9 => 1 + lineFamily A s
          (DirectC9GraphRootEvaluation.quotientLine C c₀ a)) 9 le_rfl := by
  let V : Fin 10 → (power C 9).left.Modules :=
    fun a => movingPushforward k C c₀ a.val (by omega)
  have hV : ∀ a : Fin 10,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (V a) (9 + a.val) :=
    fun a => DirectC9Bundles.movingPushforward_rank k C c₀ hg a.val (by omega)
  let L : Fin 9 → ChowCapWords.InvertibleLine (power C 9).left :=
    DirectC9GraphRootEvaluation.quotientLine C c₀
  let i : ∀ a : Fin 9, V a.castSucc ⟶ V a.succ :=
    fun a => (DirectC9MovingRows.movingRow k C c₀ hg a.val (by omega)).f
  let p : ∀ a : Fin 9, V a.succ ⟶ (L a).1 :=
    fun a => (DirectC9MovingRows.movingRow k C c₀ hg a.val (by omega)).g
  let w : ∀ a : Fin 9, i a ≫ p a = 0 :=
    fun a => (DirectC9MovingRows.movingRow k C c₀ hg a.val (by omega)).zero
  have h : ∀ a : Fin 9, (ShortComplex.mk (i a) (p a) (w a)).ShortExact :=
    fun a => DirectC9MovingRows.movingRow_shortExact k C c₀ hg a.val (by omega)
  have hw := ChowWhitneyLineTower.chernFamily_eq_ordered_line_product A s
    9 9 V hV L i p w h
  simpa only [V, L, Fin.val_last, Fin.val_zero, Nat.reduceAdd] using hw

/-- The retained original E18 has the same genuine raw product by
its actual ordinary pushforward isomorphism to the final moving stage. -/
theorem E18_chernFamily_eq_moving_product :
    @chernFamily A (power C 9).left s _ (DirectC9Bundles.E18 k C c₀) 18
      (DirectC9Bundles.E18_rank k C c₀ hg) =
    @chernFamily A (power C 9).left s _ (movingPushforward k C c₀ 0 (Nat.zero_le 9)) 9
      (by simpa using DirectC9Bundles.movingPushforward_rank k C c₀ hg 0 (Nat.zero_le 9)) *
      ChowWhitneyLineTower.orderedPrefix
        (fun a : Fin 9 => 1 + lineFamily A s
          (DirectC9GraphRootEvaluation.quotientLine C c₀ a)) 9 le_rfl := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (DirectC9Bundles.E18 k C c₀) 18 :=
    DirectC9Bundles.E18_rank k C c₀ hg
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (movingPushforward k C c₀ 9 (Nat.le_refl 9)) 18 := by
    simpa using DirectC9Bundles.movingPushforward_rank k C c₀ hg 9 (Nat.le_refl 9)
  have he : chernFamily A s (DirectC9Bundles.E18 k C c₀) 18 =
      chernFamily A s (movingPushforward k C c₀ 9 (Nat.le_refl 9)) 18 :=
    chernFamily_congr A s _ 18 (DirectC9TwistLineIsos.E18IsoMovingNine k C c₀) rfl
  exact he.trans (moving_chernFamily_eq_product k C c₀ hg A s)

end M9Native.DirectC9MovingChern

module

public import M9StacksIntegration.DualLinePicard
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public meta import Lean.Elab.Tactic.Omega

/-!
# Actual integral Chow cap signs for the actual dual line

The genuine evaluation isomorphism L-dual tensor L = O, together with
the native tensor and unit formulas of Stacks 02SP, proves the sign of
the actual dual line on cycles and Chow groups. The rank-one native
Chern cap is then the same operation. This isolates the cycle/cap part
of native GenuineChern.FirstChernClassDual without its bivariant and
general splitting-principle imports. No dual-Chern equality, chosen
tensor inverse, or formal Chern root is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.ChowLineDuality

open Stacks.Chow Stacks.Chow.GenuineChern

variable {X : Scheme.{u}} (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

local instance dualInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (dualSheaf L) :=
  DualLinePicard.dual_isInvertible L hL

def dualTensorIsoUnit : Scheme.Modules.tensorObj (dualSheaf L) L ≅
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  exact Stacks.SheafOfModules.Scheme.evaluationIso X L

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

theorem cycle_cap_dual (k : ℤ) (α : CycleGroup C q (k+1)) :
    firstChernClassCapOfInvertible C q k (dualSheaf L) α =
      -firstChernClassCapOfInvertible C q k L α := by
  rw [eq_neg_iff_add_eq_zero,
    firstChernClassCapOfInvertible_tensorObj C q k (dualSheaf L) L α,
    firstChernClassCapOfInvertible_congr C q k _ _ (dualTensorIsoUnit L) α]
  exact firstChernClassCapOfInvertible_unit C q k α

theorem chow_cap_dual (k : ℤ) (α : chowGroup C q (k+1)) :
    firstChernClassCapChow C k q (dualSheaf L) α =
      -firstChernClassCapChow C k q L α := by
  induction α using QuotientAddGroup.induction_on with
  | H β => exact cycle_cap_dual L C q k β

local instance lineRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L hL

local instance dualLineRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf L) 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X (dualSheaf L)
    (dualInvertible L)

theorem rank_one_topCap_dual (k : ℤ) (α : chowGroup C q k) :
    chernCap C 1 q (dualSheaf L) k (Fin.last 1) α =
      -chernCap C 1 q L k (Fin.last 1) α := by
  change chernCap C 1 q (dualSheaf L) k 1 α = -chernCap C 1 q L k 1 α
  rw [chernCap_one_eq_invCap C q (dualSheaf L) k α, chernCap_one_eq_invCap C q L k α]
  exact chow_cap_dual L C q (k-1) (chowGroupCast C q (by omega) α)

end M9Native.ChowLineDuality

module

public import M9StacksIntegration.ChowLineFamilyComparison
public import M9StacksIntegration.ChowVirtualPullback
public import M9StacksIntegration.LineFamilyCapPower

/-!
# Genuine flat pullback of the same actual line powers

The line, the sheaf isomorphism to its actual pullback and the native
flat Chow map are explicit. Rank one and every operational compatibility
are derived, rather than supplied as numerical or cap identities.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
universe u
namespace M9Native.LagrangianLinePullback
open ChowCapWords GradedLineCapSubring ChowLineFamilyComparison

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
    (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hf : f ≫ qX=qY) (d : ℕ) (hd : RelativeDimension f d)
    (L : InvertibleLine X) (L' : InvertibleLine Y)
    (e : L'.1 ≅ (Scheme.Modules.pullback f).obj L.1)

local instance sourceRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L.1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L.1 L.2
local instance targetRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L'.1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible Y L'.1 L'.2

include e

theorem flatPull_intertwines_lineFamily :
    Intertwines (ChowVirtualPullback.actualPull C qX qY f hf d hd)
      (lineFamily C qX L) (lineFamily C qY L') := by
  rw [lineFamily_eq_homComponent C qX L, lineFamily_eq_homComponent C qY L']
  apply (ChowVirtualPullback.intertwines_iff_lowering _ _ _).2
  exact ((ChowVirtualPullback.intertwines_iff_lowering _ _ _).1
    (intertwines_chernFamily C qX L.1 1 qY f hf d hd L'.1 e)).homComponent 1

theorem flatPull_intertwines_lineFamily_pow (s : ℕ) :
    Intertwines (ChowVirtualPullback.actualPull C qX qY f hf d hd)
      (lineFamily C qX L ^ s) (lineFamily C qY L' ^ s) := by
  apply (ChowVirtualPullback.intertwines_iff_lowering _ _ _).2
  have h := (ChowVirtualPullback.intertwines_iff_lowering _ _ _).1
    (flatPull_intertwines_lineFamily C qX qY f hf d hd L L' e)
  induction s with
  | zero => simpa only [pow_zero] using GradedCapFamily.Intertwines.one
  | succ s ih => simpa only [pow_succ] using ih.mul h

/-- Literal cap-power naturality in arbitrary displayed equal degrees. -/
theorem flatPull_capPow (s : ℕ) (a m : ℤ) (h : a=m+(s:ℤ)) (α : chowGroup C qX a) :
    ChowVirtualPullback.actualPull C qX qY f hf d hd m
        (capPow C qX (lineCap C qX L) s a m h α) =
      capPow C qY (lineCap C qY L') s (a+d) (m+d) (by omega)
        (ChowVirtualPullback.actualPull C qX qY f hf d hd a α) := by
  have hp := (flatPull_intertwines_lineFamily_pow C qX qY f hf d hd L L' e s).capTo
    s (show a-(s:ℤ)=m by omega) α
  dsimp only [capTo] at hp
  rw [LineFamilyCapPower.gradedDegreeCast_lineFamily_pow_apply C qX L s a m h α,
    LineFamilyCapPower.gradedDegreeCast_lineFamily_pow_apply C qY L' s (a+d) (m+d)
      (by omega)] at hp
  exact hp

end M9Native.LagrangianLinePullback

module

public import M9StacksIntegration.GradedLineCapSubring
public import M9StacksIntegration.ChowLineDuality
public import M9StacksIntegration.ChowVirtualDuality

/-!
# The actual line-cap family is the actual first Chern component

The named invertible line has its genuine rank-one Chern family, and
native CapRuleRankOne identifies its first component with the original
native line cap used by the direct C9 trace. Isomorphisms and the actual
dual line therefore preserve, respectively negate, that same operational
family. No numerical root realization or Chern comparison is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.ChowLineFamilyComparison

open ChowCapWords GradedLineCapSubring

variable {X : Scheme.{u}}

local instance lineRank (L : InvertibleLine X) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L.1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L.1 L.2

/-- The literal dual of the original named actual line. -/
def dualLine (L : InvertibleLine X) : InvertibleLine X :=
  ⟨dualSheaf L.1, DualLinePicard.dual_isInvertible L.1 L.2⟩

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- The direct native line-cap family is the first homogeneous
component of the genuine rank-one Chern family. -/
theorem lineFamily_eq_homComponent (L : InvertibleLine X) :
    lineFamily C q L = homComponent 1 (chernFamily C q L.1 1) := by
  funext k i
  by_cases hi : i = 1
  · subst i
    apply AddMonoidHom.ext
    intro α
    rw [lineFamily_apply_one, homComponent_apply_self,
      chernFamily_apply_of_le C q L.1 1 k (by omega : 1 ≤ 1)]
    change _ = chernCap C 1 q L.1 k 1 α
    calc
      _ = (invCap C q L.1).capOnChow C q (k-1)
          (chowGroupCast C q (show k = k-1+1 by omega) α) :=
        eq_of_heq (capOnChow_heq C q (lineCap C q L) rfl
          ((gradedDegreeCast_heq _ α).trans (chowGroupCast_heq C q _ α).symm))
      _ = _ := (chernCap_one_eq_invCap C q L.1 k α).symm
  · rw [lineFamily_homogeneous C q L k i hi, homComponent_apply_of_ne hi]

/-- The full actual rank-one Chern family is precisely one plus the
same actual line cap used by the integer trace. -/
theorem chernFamily_eq_one_add_lineFamily (L : InvertibleLine X) :
    chernFamily C q L.1 1 = 1 + lineFamily C q L := by
  funext k i
  change chernFamily C q L.1 1 k i =
    (1 : GradedCapFamily (chowGroup C q)) k i + lineFamily C q L k i
  cases i with
  | zero =>
    rw [chernFamily_apply_zero,
      lineFamily_homogeneous C q L k 0 (by decide), add_zero]
  | succ i =>
    cases i with
    | zero =>
      change chernFamily C q L.1 1 k 1 =
        (1 : GradedCapFamily (chowGroup C q)) k 1 + lineFamily C q L k 1
      have hzero : (1 : GradedCapFamily (chowGroup C q)) k 1 = 0 :=
        gradedCap_one_of_ne (by decide) k
      rw [hzero, zero_add]
      have h := congrArg (fun a : GradedCapFamily (chowGroup C q) => a k 1)
        (lineFamily_eq_homComponent C q L)
      simpa only [homComponent_apply_self] using h.symm
    | succ i =>
      rw [chernFamily_apply_of_gt C q L.1 1 k (by omega),
        gradedCap_one_of_ne (by omega),
        lineFamily_homogeneous C q L k (i+1+1) (by omega), zero_add]

/-- A genuine isomorphism of the named lines gives equality of their
original operational line families. -/
theorem lineFamily_congr (L M : InvertibleLine X) (e : L.1 ≅ M.1) :
    lineFamily C q L = lineFamily C q M := by
  funext k i
  by_cases hi : i = 1
  · subst i
    apply AddMonoidHom.ext
    intro α
    rw [lineFamily_apply_one, lineFamily_apply_one]
    let := L.2
    let := M.2
    exact ChowCapWords.invCap_congr C q L.1 M.1 e (k-1) _
  · rw [lineFamily_homogeneous C q L k i hi,
      lineFamily_homogeneous C q M k i hi]

/-- The actual dual-line family is the negative original line family,
on every original integral Chow group. -/
theorem lineFamily_dual (L : InvertibleLine X) :
    lineFamily C q (dualLine L) = -lineFamily C q L := by
  funext k i
  by_cases hi : i = 1
  · subst i
    apply AddMonoidHom.ext
    intro α
    change lineFamily C q (dualLine L) k 1 α = -lineFamily C q L k 1 α
    rw [lineFamily_apply_one, lineFamily_apply_one]
    let := L.2
    exact ChowLineDuality.chow_cap_dual L.1 C q (k-1) _
  · rw [lineFamily_homogeneous C q (dualLine L) k i hi]
    change 0 = -(lineFamily C q L k i)
    rw [lineFamily_homogeneous C q L k i hi, neg_zero]

/-- The corresponding genuine homogeneous Chern components have the
same proved negative sign, with the literal original named line. -/
theorem homComponent_dualLine (L : InvertibleLine X) :
    homComponent 1 (chernFamily C q (dualLine L).1 1) =
      -homComponent 1 (chernFamily C q L.1 1) := by
  rw [← lineFamily_eq_homComponent, ← lineFamily_eq_homComponent, lineFamily_dual]

/-- The actual dual line contributes one minus the original actual
line-cap family to every Whitney product. -/
theorem chernFamily_dualLine (L : InvertibleLine X) :
    chernFamily C q (dualLine L).1 1 = 1 - lineFamily C q L := by
  rw [chernFamily_eq_one_add_lineFamily, lineFamily_dual, sub_eq_add_neg]

end M9Native.ChowLineFamilyComparison

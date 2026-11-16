module

public import M9StacksIntegration.GradedCapVirtualSchur
public import M9StacksIntegration.ChowLineFamilyComparison
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PowerSumShortExact

/-!
# Actual Chern and inverse families commute with the original line caps

Native `GenuineChern.commute_chernFamily` already proves whole-family
commutation from genuine cap commutation, including the actual zero
coefficients above rank. The actual rank-one total-Chern comparison then
gives commutation with the same original native line-cap family.
Native Chern units extend this to the actual inverse and virtual
families. The ambient operational ring has only its native Ring
structure; no global commutativity premise or instance is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.ChowChernLineCommutation
open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
open M9Native.GradedCapVirtualSchur M9Native.GradedLineCapSubring

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q]

/-- The genuine total Chern cap family commutes with the very same
original native line-cap family. The line's rank one is derived from
its actual invertibility. -/
theorem chernFamily_commute_lineFamily (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E r]
    (L : ChowCapWords.InvertibleLine X) :
    Commute (chernFamily C q E r) (lineFamily C q L) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank L.1 1 :=
    @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L.1 L.2
  have h := GenuineChern.commute_chernFamily C q E r L.1 1
  rw [ChowLineFamilyComparison.chernFamily_eq_one_add_lineFamily C q L] at h
  have heq := h.eq
  simp only [mul_add, mul_one, add_mul, one_mul] at heq
  change chernFamily C q E r * lineFamily C q L =
    lineFamily C q L * chernFamily C q E r
  exact add_left_cancel heq

/-- The actual inverse selected by genuine c0=id commutes with the
original line cap. Invertibility is proved by native Chern theory. -/
theorem inverseFamily_commute_lineFamily (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E r]
    (L : ChowCapWords.InvertibleLine X) :
    Commute (inverseFamily C q E r) (lineFamily C q L) := by
  dsimp only [inverseFamily]
  apply Commute.units_inv_left
  simpa only [IsUnit.unit_spec] using chernFamily_commute_lineFamily C q E r L

/-- The actual ordered virtual family c(F)c(E)^{-1} commutes with the
same original line cap, by the two genuine factor commutations. -/
theorem virtualFamily_commute_lineFamily (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE]
    (L : ChowCapWords.InvertibleLine X) :
    Commute (virtualFamily C q F E rF rE) (lineFamily C q L) := by
  have hF := chernFamily_commute_lineFamily C q F rF L
  have hE := inverseFamily_commute_lineFamily C q E rE L
  change (chernFamily C q F rF * inverseFamily C q E rE) * lineFamily C q L =
    lineFamily C q L * (chernFamily C q F rF * inverseFamily C q E rE)
  rw [mul_assoc, hE.eq, ← mul_assoc, hF.eq, mul_assoc]

end M9Native.ChowChernLineCommutation

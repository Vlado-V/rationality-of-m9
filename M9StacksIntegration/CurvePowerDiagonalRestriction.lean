module

public import M9StacksIntegration.CurvePowerDiagonalJoinCanonical
public import M9StacksIntegration.CurvePowerDiagonalMarkedRestriction
public import M9StacksIntegration.CurvePowerDiagonalSelfRestriction

/-!
# The actual full diagonalStep rule

Every branch is proved by the corresponding original geometric cap:
marked coordinates give zero or a point, distinct free blocks join,
and a repeated block contributes the actual degree of its self line.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerDiagonalRestriction

open CurvePowerGraphLocal CurvePowerGraphDisjoint CurvePowerChowFunctional
open CurvePowerDiagonalSelfRestriction

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

theorem tautologicalFunctional_diagonal_step (ambient : ℕ) (i j : Fin ambient)
    (tail : List (Letter ambient)) (s : State)
    (hp : s.Pairwise MaskDisjoint) (hn : ∀ a ∈ s, a ≠ 0) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) s =
      match diagonalStep i.val j.val s with
      | none => 0
      | some (s', loop) => if loop then
          selfDegree k C hC * tautologicalFunctional k C c₀ ambient tail s'
        else tautologicalFunctional k C c₀ ambient tail s' := by
  have hs := nodup_of_pairwise_nonzero s hp hn
  have hsep := separated_of_pairwise s hp
  by_cases ha : blockAt i.val s = 0
  · by_cases hb : blockAt j.val s = 0
    · have h := ChowPicardCapWords.tautologicalFunctional_cons_diagonal_both_marked
        k C c₀ ambient i j tail s
        ((CurvePowerPointRestriction.blockAt_eq_zero_iff i.val s).mp ha)
        ((CurvePowerPointRestriction.blockAt_eq_zero_iff j.val s).mp hb)
      simpa only [diagonalStep, ha, hb, ite_true] using h
    · have hm := CurvePowerDiagonalMarkedRestriction.tautologicalFunctional_diagonal_left_marked
        k C c₀ ambient s i j tail
        ((CurvePowerPointRestriction.blockAt_eq_zero_iff i.val s).mp ha)
      have hspec := CurvePowerPointRestriction.blockAt_mem_and_testBit j.val s hb
      have hf := CurvePowerPointRestriction.tautologicalFunctional_point_free_block
        k C c₀ hC ambient j tail s hs hsep (blockAt j.val s) hspec.1 hspec.2
      simpa only [diagonalStep, ha, hb, Bool.false_eq_true, ite_true, ite_false] using hm.trans hf
  · have hspecI := CurvePowerPointRestriction.blockAt_mem_and_testBit i.val s ha
    by_cases hb : blockAt j.val s = 0
    · have hm := CurvePowerDiagonalMarkedRestriction.tautologicalFunctional_diagonal_right_marked
        k C c₀ ambient s i j tail
        ((CurvePowerPointRestriction.blockAt_eq_zero_iff j.val s).mp hb)
      have hf := CurvePowerPointRestriction.tautologicalFunctional_point_free_block
        k C c₀ hC ambient i tail s hs hsep (blockAt i.val s) hspecI.1 hspecI.2
      simpa only [diagonalStep, ha, hb, Bool.false_eq_true, ite_true, ite_false] using hm.trans hf
    · have hspecJ := CurvePowerPointRestriction.blockAt_mem_and_testBit j.val s hb
      by_cases hab : blockAt i.val s = blockAt j.val s
      · have hj : (blockAt i.val s).testBit j.val = true := by
          rw [hab]
          exact hspecJ.2
        have h := tautologicalFunctional_diagonal_same_block k C c₀ hC ambient i j tail
          s hs hsep (blockAt i.val s) hspecI.1 hspecI.2 hj
        simpa only [diagonalStep, ha, hb, hab, ite_true, ite_false] using h
      · have h := CurvePowerDiagonalJoinCanonical.tautologicalFunctional_diagonal_free_blocks_canonical
          k C c₀ hC ambient i j tail s hp hn (blockAt i.val s) (blockAt j.val s)
          hspecI.1 hspecJ.1 hab hspecI.2 hspecJ.2
        simpa only [diagonalStep, ha, hb, hab, Bool.false_eq_true, ite_true, ite_false] using h

end M9Native.CurvePowerDiagonalRestriction

module

public import M9StacksIntegration.CurvePowerFullState
public import M9StacksIntegration.CurvePowerDiagonalRestriction

/-! Genuine point/diagonal word relations on the original whole curve
power. These are integer identities of the actual Chow-cap degree, derived
from actual partition restriction, rather than Picard-class identities. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.CurvePower

universe u
namespace M9Native.CurvePowerActualWordRelations

open CurvePowerGraphLocal CurvePowerGraphMapReindex CurvePowerGraphDisjoint
open CurvePowerGraphContextSelection CurvePowerChowFunctional CurvePowerFullState
open CurvePowerPointRestriction CurvePowerDiagonalSelfRestriction

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

local notation "F" => (tautologicalFunctional k C c₀)
local notation "W" => (CurvePowerPointTrace.actualWordDegree k C c₀)

include hC

theorem point_square_state (n : ℕ) (i : Fin n) (tail : List (Letter n))
    (s : State) (hs : s.Nodup) (hp : s.Pairwise MaskDisjoint) :
    F n (.inl i :: .inl i :: tail) s = 0 := by
  rw [tautologicalFunctional_point_step k C c₀ hC n i (.inl i :: tail) s hs
    (separated_of_pairwise s hp)]
  by_cases hb : blockAt i.val s = 0
  · simp only [pointStep, hb, ite_true]
  · simp only [pointStep, hb, ite_false]
    let s' := s.erase (blockAt i.val s)
    have hs' : s'.Nodup := hs.erase _
    have hp' : s'.Pairwise MaskDisjoint := hp.erase _
    have hm : blockAt i.val s' = 0 :=
      (CurvePowerPointRestriction.blockAt_eq_zero_iff i.val s').mpr
        (erase_blockAt_misses i.val s hp hs)
    rw [tautologicalFunctional_point_step k C c₀ hC n i tail s' hs'
      (separated_of_pairwise s' hp')]
    simp only [pointStep, hm, ite_true]

theorem word_point_square (n : ℕ) (i : Fin n) (tail : List (Letter n)) :
    W n (.inl i :: .inl i :: tail) = 0 := by
  rw [← tautologicalFunctional_fullState k C c₀ n (.inl i :: .inl i :: tail)]
  exact point_square_state k C c₀ hC n i tail (fullState n)
    (fullState_nodup n) (fullState_pairwise n)

theorem word_point_diagonal (n : ℕ) (i j : Fin n) (tail : List (Letter n)) :
    W n (.inl i :: .inr (i,j) :: tail) = W n (.inl i :: .inl j :: tail) := by
  rw [← tautologicalFunctional_fullState k C c₀ n (.inl i :: .inr (i,j) :: tail),
    ← tautologicalFunctional_fullState k C c₀ n (.inl i :: .inl j :: tail)]
  rw [tautologicalFunctional_point_step k C c₀ hC n i (.inr (i,j) :: tail)
      (fullState n) (fullState_nodup n) (fullState_separated n),
    tautologicalFunctional_point_step k C c₀ hC n i (.inl j :: tail)
      (fullState n) (fullState_nodup n) (fullState_separated n)]
  simp only [pointStep_fullState]
  let s := (fullState n).erase (bit i.val)
  have hs : s.Nodup := (fullState_nodup n).erase _
  have hp : s.Pairwise MaskDisjoint := (fullState_pairwise n).erase _
  have hn : ∀ a ∈ s, a ≠ 0 := fun a ha =>
    fullState_nonzero n a (List.mem_of_mem_erase ha)
  have hmiss : ∀ a ∈ s, a.testBit i.val = false := by
    simpa only [s, blockAt_fullState] using
      (erase_blockAt_misses i.val (fullState n) (fullState_pairwise n) (fullState_nodup n))
  have hm : blockAt i.val s = 0 :=
    (CurvePowerPointRestriction.blockAt_eq_zero_iff i.val s).mpr hmiss
  rw [CurvePowerDiagonalRestriction.tautologicalFunctional_diagonal_step
      k C c₀ hC n i j tail s hp hn,
    tautologicalFunctional_point_step k C c₀ hC n j tail s hs (separated_of_pairwise s hp)]
  by_cases hj : blockAt j.val s = 0
  · simp only [diagonalStep, pointStep, hm, hj, ite_true]
  · simp only [diagonalStep, pointStep, hm, hj, ite_true, ite_false, Bool.false_eq_true]

theorem diagonal_self_state (n : ℕ) (i : Fin n) (tail : List (Letter n))
    (s : State) (hp : s.Pairwise MaskDisjoint) (hn : ∀ a ∈ s, a ≠ 0) :
    F n (.inr (i,i) :: tail) s = selfDegree k C hC * F n (.inl i :: tail) s := by
  have hs := nodup_of_pairwise_nonzero s hp hn
  rw [CurvePowerDiagonalRestriction.tautologicalFunctional_diagonal_step
      k C c₀ hC n i i tail s hp hn,
    tautologicalFunctional_point_step k C c₀ hC n i tail s hs (separated_of_pairwise s hp)]
  by_cases hb : blockAt i.val s = 0
  · simp only [diagonalStep, pointStep, hb, ite_true, mul_zero]
  · simp only [diagonalStep, pointStep, hb, ite_false, ite_true]

theorem word_diagonal_self (n : ℕ) (i : Fin n) (tail : List (Letter n)) :
    W n (.inr (i,i) :: tail) = selfDegree k C hC * W n (.inl i :: tail) := by
  rw [← tautologicalFunctional_fullState k C c₀ n (.inr (i,i) :: tail),
    ← tautologicalFunctional_fullState k C c₀ n (.inl i :: tail)]
  exact diagonal_self_state k C c₀ hC n i tail (fullState n)
    (fullState_pairwise n) (fullState_nonzero n)

end M9Native.CurvePowerActualWordRelations

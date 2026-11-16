module

public import M9StacksIntegration.CurvePowerActualWordRelations
public import M9StacksIntegration.CurvePowerDiagonalJoinCanonical

/-! The square of an actual diagonal, paired with every remaining word
on the original curve power. Joining two free blocks and restricting the
second diagonal to the actual self-diagonal gives its genuine degree. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurvePowerActualDiagonalSquare

open CurvePowerGraphLocal CurvePowerGraphMapReindex CurvePowerGraphDisjoint
open CurvePowerChowFunctional CurvePowerFullState CurvePowerPointRestriction
open CurvePowerDiagonalSelfRestriction CurvePowerDiagonalJoinRestriction
open CurvePowerDiagonalJoinCanonical CurvePowerActualWordRelations

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

local notation "F" => (tautologicalFunctional k C c₀)
local notation "W" => (CurvePowerPointTrace.actualWordDegree k C c₀)

include hC

theorem diagonal_square_free_blocks (n : ℕ) (i j : Fin n) (tail : List (Letter n))
    (s : State) (hp : s.Pairwise MaskDisjoint) (hn : ∀ c ∈ s, c ≠ 0)
    (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true) :
    F n (.inr (i,j) :: .inr (i,j) :: tail) s =
      selfDegree k C hC * F n (.inl i :: .inl j :: tail) s := by
  have hs : s.Nodup := nodup_of_pairwise_nonzero s hp hn
  have hsep := separated_of_pairwise s hp
  have hjoin := joined_pairwise hp a b ha hb hab
  have hsepj := separated_of_pairwise _ hjoin
  have hai : (a ||| b).testBit i.val = true := by
    simp only [Nat.testBit_or, hi, Bool.true_or]
  have hbj : (a ||| b).testBit j.val = true := by
    simp only [Nat.testBit_or, hj, Bool.or_true]
  have hbt : b ∈ s.erase a := (List.mem_erase_of_ne (Ne.symm hab)).mpr hb
  have hp' : (s.erase a).Pairwise MaskDisjoint := hp.erase _
  have hr := tautologicalFunctional_point_free_block k C c₀ hC n i
    (.inl j :: tail) s hs hsep a ha hi
  have hr' := tautologicalFunctional_point_free_block k C c₀ hC n j tail
    (s.erase a) (hs.erase _) (separated_of_pairwise _ hp') b hbt hj
  rw [tautologicalFunctional_diagonal_free_blocks k C c₀ hC n i j
    (.inr (i,j) :: tail) s hs hsep a b ha hb hab hi hj]
  rw [tautologicalFunctional_diagonal_same_head k C c₀ hC n (a ||| b)
    ((s.erase a).erase b) i j tail hai hbj hsepj, hr, hr']

theorem word_diagonal_square_distinct (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (tail : List (Letter n)) :
    W n (.inr (i,j) :: .inr (i,j) :: tail) =
      selfDegree k C hC * W n (.inl i :: .inl j :: tail) := by
  have hab : bit i.val ≠ bit j.val := by
    intro he
    have ht : (bit i.val).testBit j.val = true := by
      rw [he]
      exact Nat.testBit_two_pow_self
    have hv : i.val = j.val := by
      simpa only [bit, Nat.testBit_two_pow, decide_eq_true_eq] using ht
    exact hij (Fin.ext hv)
  rw [← tautologicalFunctional_fullState k C c₀ n (.inr (i,j) :: .inr (i,j) :: tail),
    ← tautologicalFunctional_fullState k C c₀ n (.inl i :: .inl j :: tail)]
  exact diagonal_square_free_blocks k C c₀ hC n i j tail (fullState n)
    (fullState_pairwise n) (fullState_nonzero n) (bit i.val) (bit j.val)
    (mem_fullState i) (mem_fullState j) hab
    Nat.testBit_two_pow_self Nat.testBit_two_pow_self

theorem word_diagonal_square (n : ℕ) (i j : Fin n) (tail : List (Letter n)) :
    W n (.inr (i,j) :: .inr (i,j) :: tail) =
      selfDegree k C hC * W n (.inl i :: .inl j :: tail) := by
  by_cases hij : i = j
  · subst j
    rw [word_diagonal_self k C c₀ hC n i (.inr (i,i) :: tail),
      word_point_diagonal k C c₀ hC n i i tail]
  · exact word_diagonal_square_distinct k C c₀ hC n i j hij tail

end M9Native.CurvePowerActualDiagonalSquare

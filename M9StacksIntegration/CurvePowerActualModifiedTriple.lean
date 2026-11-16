module

public import M9StacksIntegration.CurvePowerActualTraceNormalization
public import M9StacksIntegration.CurvePowerFullStateThree
public import M9StacksIntegration.CurvePowerThreeBlockContext
public import M9StacksIntegration.CurvePowerThreeBlockWords

/-! The genuine modified small-diagonal relation on the whole original
curve power, paired with every word. Its quotient cross identity follows
from the actual geometric restriction and vanishing theorems. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurvePowerActualModifiedTriple

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphDisjoint
open CurvePowerGraphInduction CurvePowerChowFunctional CurvePowerPointTrace
open CurvePowerDiagonalSelfRestriction CurvePowerThreeBlockWords
open CurvePowerFullStateThree CurvePowerActualTraceRelations

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

local notation "F" => (tautologicalFunctional k C c₀)
local notation "W" => (actualWordDegree k C c₀)

include hC

theorem modifiedTriple_state (n a b c : ℕ) (s : State) (i j l : Fin n)
    (tail : List (Letter n)) (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    F n (.inr (i,l) :: .inr (j,l) :: tail) (a :: b :: c :: s) -
      F n (.inr (i,l) :: .inl j :: tail) (a :: b :: c :: s) -
      F n (.inr (j,l) :: .inl i :: tail) (a :: b :: c :: s) -
      F n (.inr (i,j) :: .inl l :: tail) (a :: b :: c :: s) +
      F n (.inl i :: .inl j :: tail) (a :: b :: c :: s) +
      F n (.inl i :: .inl l :: tail) (a :: b :: c :: s) +
      F n (.inl j :: .inl l :: tail) (a :: b :: c :: s) = 0 := by
  let frame := CurvePowerThreeBlockContext.frame a b c s hp hn
  have hz := CurvePowerGammaVanishing.gammaValue_eq_zero k C c₀ hC n frame tail
  change realization (selfDegree k C hC) (F n tail ∘ transport frame.val)
    (embed localGamma) = 0 at hz
  have he := CurvePowerThreeBlockContext.realization_frame (selfDegree k C hC)
    (F n tail) a b c s hp hn
  have hv := he.symm.trans hz
  rw [diagonal_diagonal_canonical k C c₀ hC n a b c s i j l tail hp hn hi hj hl,
    diagonal_point_ac_canonical k C c₀ hC n a b c s i j l tail hp hn hi hj hl,
    diagonal_point_bc_canonical k C c₀ hC n a b c s i j l tail hp hn hi hj hl,
    diagonal_point_ab_canonical k C c₀ hC n a b c s i j l tail hp hn hi hj hl,
    point_point_ab_canonical k C c₀ hC n a b c s i j l tail hp hn hi hj hl,
    point_point_ac_canonical k C c₀ hC n a b c s i j l tail hp hn hi hj hl,
    point_point_bc_canonical k C c₀ hC n a b c s i j l tail hp hn hi hj hl]
  linear_combination hv

theorem word_modifiedTriple_distinct (n : ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (tail : List (Letter n)) :
    W n (.inr (i,l) :: .inr (j,l) :: tail) - W n (.inr (i,l) :: .inl j :: tail) -
      W n (.inr (j,l) :: .inl i :: tail) - W n (.inr (i,j) :: .inl l :: tail) +
      W n (.inl i :: .inl j :: tail) + W n (.inl i :: .inl l :: tail) +
      W n (.inl j :: .inl l :: tail) = 0 := by
  simp only [actualWordDegree_three k C c₀ n i j l hij hil hjl]
  exact modifiedTriple_state k C c₀ hC n (bit i.val) (bit j.val) (bit l.val)
    (remaining n i j l) i j l tail (three_pairwise n i j l hij hil hjl)
    (three_nonzero n i j l hij hil hjl) Nat.testBit_two_pow_self
    Nat.testBit_two_pow_self Nat.testBit_two_pow_self

theorem modifiedTriple_distinct (n : ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    CurvePowerDiagonalAlgebra.modifiedTriple
      (point k C c₀ n i) (point k C c₀ n j) (point k C c₀ n l)
      (diagonal k C c₀ n i j) (diagonal k C c₀ n i l) (diagonal k C c₀ n j l) = 0 :=
  PolynomialTraceRelations.pointClass_modifiedTriple (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (.inl i) (.inl j) (.inl l)
    (.inr (i,j)) (.inr (i,l)) (.inr (j,l))
    (word_modifiedTriple_distinct k C c₀ hC n i j l hij hil hjl)

theorem reducedDiagonal_cross_distinct (n : ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    reducedDiagonal k C c₀ n i l * reducedDiagonal k C c₀ n j l =
      point k C c₀ n l * reducedDiagonal k C c₀ n i j :=
  PolynomialTraceRelations.reducedDiagonal_cross (actualWordDegree k C c₀ n)
    (actualWordDegree_perm k C c₀ n) (.inl i) (.inl j) (.inl l)
    (.inr (i,j)) (.inr (i,l)) (.inr (j,l))
    (CurvePowerActualWordRelations.word_point_square k C c₀ hC n l)
    (word_point_diagonal_right k C c₀ hC n i l)
    (word_point_diagonal_right k C c₀ hC n j l)
    (word_modifiedTriple_distinct k C c₀ hC n i j l hij hil hjl)

end M9Native.CurvePowerActualModifiedTriple

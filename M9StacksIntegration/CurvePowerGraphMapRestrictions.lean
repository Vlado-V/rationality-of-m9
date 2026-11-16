module

public import M9StacksIntegration.CurvePowerGraphMaps
public import Mathlib.Data.Nat.Bitwise

/-!
# Genuine point and diagonal restriction maps of partitions

These maps use only finite products of the actual curve over the actual
base. The point insertion and coordinate doubling are the same literal
lifts used by the native intersection restriction theorems. No degree,
intersection, or numerical equivalence assertion is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphMapRestrictions

open CurvePowerGraphLocal CurvePowerGraphMaps

variable {S : Scheme.{u}} (C : Over S) (c₀ : power C 0 ⟶ C)

/-- Literal insertion lift, identical to the native insertion formula. -/
def insertConstant (m : ℕ) (i : Fin (m + 1)) : power C m ⟶ power C (m + 1) :=
  lift (m + 1) (Fin.insertNth i (toUnit (power C m) ≫ c₀) (coord C m))

@[reassoc (attr := simp)]
theorem insertConstant_coord_self (m : ℕ) (i : Fin (m + 1)) :
    insertConstant C c₀ m i ≫ coord C (m + 1) i = toUnit (power C m) ≫ c₀ := by
  rw [insertConstant, lift_coord, Fin.insertNth_apply_same]

@[reassoc (attr := simp)]
theorem insertConstant_coord_succAbove (m : ℕ) (i : Fin (m + 1)) (j : Fin m) :
    insertConstant C c₀ m i ≫ coord C (m + 1) (i.succAbove j) = coord C m j := by
  rw [insertConstant, lift_coord, Fin.insertNth_apply_succAbove]

theorem insertConstant_zero_fst (m : ℕ) :
    insertConstant C c₀ m 0 ≫ fst C (power C m) = toUnit (power C m) ≫ c₀ := by
  exact insertConstant_coord_self C c₀ m 0

theorem insertConstant_zero_snd (m : ℕ) :
    insertConstant C c₀ m 0 ≫ snd C (power C m) = 𝟙 (power C m) := by
  apply Stacks.CurvePower.hom_ext m
  intro j
  rw [Category.assoc, ← coord_succ]
  simpa only [Fin.succAbove_zero, Category.id_comp] using
    insertConstant_coord_succAbove C c₀ m 0 j

/-- Pinning a block replaces its genuine coordinate by the fixed point.
Disjointness ensures that its vertices are marked in the smaller state. -/
theorem insertConstant_stateCoordinate (b : ℕ) (s : State) (i : ℕ)
    (hdisjoint : b.testBit i = true → ∀ a ∈ s, a.testBit i = false) :
    insertConstant C c₀ s.length 0 ≫ stateCoordinate C c₀ (b :: s) i =
      stateCoordinate C c₀ s i := by
  cases hi : b.testBit i with
  | false =>
      rw [stateCoordinate_cons_of_not_mem C c₀ b s i hi, ← Category.assoc,
        insertConstant_zero_snd, Category.id_comp]
  | true =>
      rw [stateCoordinate_cons_of_mem C c₀ b s i hi, insertConstant_zero_fst,
        stateCoordinate_eq_fixed C c₀ s i (hdisjoint hi)]

theorem insertConstant_stateMap (ambient b : ℕ) (s : State)
    (hdisjoint : ∀ i : Fin ambient, b.testBit i.val = true →
      ∀ a ∈ s, a.testBit i.val = false) :
    insertConstant C c₀ s.length 0 ≫ stateMap C c₀ ambient (b :: s) =
      stateMap C c₀ ambient s := by
  apply Stacks.CurvePower.hom_ext ambient
  intro i
  simp only [Category.assoc, stateMap_coord]
  exact insertConstant_stateCoordinate C c₀ b s i.val (hdisjoint i)

/-- Literal coordinate doubling, identical to the native double-first lift. -/
def duplicateFirst (m : ℕ) : power C (m + 1) ⟶ power C (m + 2) :=
  lift (m + 2) (Fin.cons (coord C (m + 1) 0) (coord C (m + 1)))

theorem duplicateFirst_fst (m : ℕ) :
    duplicateFirst C m ≫ fst C (power C (m + 1)) = fst C (power C m) := by
  simp only [duplicateFirst, lift_succ_fst, Fin.cons_zero, coord_zero]

theorem duplicateFirst_snd (m : ℕ) :
    duplicateFirst C m ≫ snd C (power C (m + 1)) = 𝟙 (power C (m + 1)) := by
  apply Stacks.CurvePower.hom_ext (m + 1)
  intro i
  rw [Category.assoc, ← coord_succ]
  simp only [duplicateFirst, lift_coord, Fin.cons_succ, Category.id_comp]

/-- The actual diagonal map identifies two blocks by their literal union. -/
theorem duplicateFirst_stateCoordinate (a b : ℕ) (s : State) (i : ℕ) :
    duplicateFirst C s.length ≫ stateCoordinate C c₀ (a :: b :: s) i =
      stateCoordinate C c₀ ((a ||| b) :: s) i := by
  cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    simp only [stateCoordinate, List.length_cons, ha, hb, Nat.testBit_lor,
      Bool.or_false, Bool.or_true, Bool.false_eq_true, ite_true, ite_false,
      ← Category.assoc, duplicateFirst_fst, duplicateFirst_snd, Category.id_comp]

theorem duplicateFirst_stateMap (ambient a b : ℕ) (s : State) :
    duplicateFirst C s.length ≫ stateMap C c₀ ambient (a :: b :: s) =
      stateMap C c₀ ambient ((a ||| b) :: s) := by
  apply Stacks.CurvePower.hom_ext ambient
  intro i
  simp only [Category.assoc, stateMap_coord]
  exact duplicateFirst_stateCoordinate C c₀ a b s i.val

end M9Native.CurvePowerGraphMapRestrictions

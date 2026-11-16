module

public import M9StacksIntegration.CurvePowerGraphLocal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePower

/-!
# Genuine partition maps between the native curve powers

An unmarked block supplies one variable curve coordinate. Vertices in
that block receive this coordinate; every marked vertex receives the
actual fixed point. The construction works over any base scheme and
uses only the native finite-product universal property.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphMaps

open CurvePowerGraphLocal

variable {S : Scheme.{u}} (C : Over S) (c₀ : power C 0 ⟶ C)

/-- The actual relative point represented by one vertex of a partition.
The first block containing that vertex supplies its actual coordinate. -/
def stateCoordinate : (s : State) → ℕ → (power C s.length ⟶ C)
  | [], _ => c₀
  | b :: s, i =>
      if b.testBit i then fst C (power C s.length)
      else snd C (power C s.length) ≫ stateCoordinate s i

/-- The genuine map realizing a partition with its marked vertices. -/
def stateMap (n : ℕ) (s : State) : power C s.length ⟶ power C n :=
  lift n fun i => stateCoordinate C c₀ s i.val

@[reassoc (attr := simp)]
theorem stateMap_coord (n : ℕ) (s : State) (i : Fin n) :
    stateMap C c₀ n s ≫ coord C n i = stateCoordinate C c₀ s i.val := by
  exact lift_coord n _ i

theorem stateCoordinate_cons_of_mem (b : ℕ) (s : State) (i : ℕ)
    (hi : b.testBit i = true) :
    stateCoordinate C c₀ (b :: s) i = fst C (power C s.length) := by
  simp [stateCoordinate, hi]

theorem stateCoordinate_cons_of_not_mem (b : ℕ) (s : State) (i : ℕ)
    (hi : b.testBit i = false) :
    stateCoordinate C c₀ (b :: s) i =
      snd C (power C s.length) ≫ stateCoordinate C c₀ s i := by
  simp [stateCoordinate, hi]

/-- A marked vertex factors through the actual base point. -/
theorem stateCoordinate_eq_fixed (s : State) (i : ℕ)
    (hi : ∀ b ∈ s, b.testBit i = false) :
    stateCoordinate C c₀ s i = toUnit (power C s.length) ≫ c₀ := by
  induction s with
  | nil =>
      change c₀ = toUnit (power C 0) ≫ c₀
      rw [show toUnit (power C 0) = 𝟙 (power C 0) from toUnit_unique _ _, Category.id_comp]
  | cons b s ih =>
      rw [stateCoordinate_cons_of_not_mem C c₀ b s i (hi b (by simp)),
        ih (fun a ha => hi a (by simp [ha])), ← Category.assoc]
      exact congrArg (fun f => f ≫ c₀) (toUnit_unique _ _)

/-- The selected block supplies its literal coordinate. The condition
on preceding blocks is supplied by pairwise disjointness for partitions. -/
theorem stateCoordinate_eq_coord (s : State) (i : ℕ) (j : Fin s.length)
    (hj : (s.get j).testBit i = true)
    (hprev : ∀ q : Fin s.length, q.val < j.val → (s.get q).testBit i = false) :
    stateCoordinate C c₀ s i = coord C s.length j := by
  induction s with
  | nil => exact j.elim0
  | cons b s ih =>
      cases j using Fin.cases with
      | zero =>
          change b.testBit i = true at hj
          rw [stateCoordinate_cons_of_mem C c₀ b s i hj]
          rfl
      | succ j =>
          have hb : b.testBit i = false := hprev 0 (by
            simpa only [Fin.val_zero, Fin.val_succ] using Nat.zero_lt_succ j.val)
          have ht : (s.get j).testBit i = true := hj
          rw [stateCoordinate_cons_of_not_mem C c₀ b s i hb,
            ih j ht (fun q hq => hprev q.succ (by simpa using hq))]
          rfl

theorem stateMap_pair (n : ℕ) (s : State) (i j : Fin n) :
    stateMap C c₀ n s ≫ reindex C ![i, j] =
      lift 2 ![stateCoordinate C c₀ s i.val, stateCoordinate C c₀ s j.val] := by
  apply hom_ext 2
  intro q
  fin_cases q <;> simp only [Category.assoc, reindex_coord, stateMap_coord, lift_coord] <;> rfl

/-- The partition map on five active blocks, with all other genuine
curve coordinates left as spectators. No product-model identification
is assumed: every displayed coordinate is specified by a genuine lift. -/
def stateMapWithSpectators (n : ℕ) (s : State) :
    power C (s.length + n) ⟶ power C (5 + n) :=
  lift (5 + n) (Fin.addCases
    (fun i : Fin 5 => reindex C (Fin.castAdd n) ≫ stateCoordinate C c₀ s i.val)
    (fun j : Fin n => coord C (s.length + n) (Fin.natAdd s.length j)))

@[reassoc (attr := simp)]
theorem stateMapWithSpectators_active (n : ℕ) (s : State) (i : Fin 5) :
    stateMapWithSpectators C c₀ n s ≫ coord C (5 + n) (Fin.castAdd n i) =
      reindex C (Fin.castAdd n) ≫ stateCoordinate C c₀ s i.val := by
  simp only [stateMapWithSpectators, lift_coord, Fin.addCases_left]

@[reassoc (attr := simp)]
theorem stateMapWithSpectators_spectator (n : ℕ) (s : State) (j : Fin n) :
    stateMapWithSpectators C c₀ n s ≫ coord C (5 + n) (Fin.natAdd 5 j) =
      coord C (s.length + n) (Fin.natAdd s.length j) := by
  simp only [stateMapWithSpectators, lift_coord, Fin.addCases_right]

end M9Native.CurvePowerGraphMaps

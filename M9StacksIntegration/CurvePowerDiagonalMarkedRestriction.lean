module

public import M9StacksIntegration.CurvePowerPointRestriction
public import M9StacksIntegration.CurvePowerGraphFixedRestrictions

/-!
# Actual mixed marked/free diagonal restriction

A marked coordinate factors through the actual fixed point. The
diagonal line therefore restricts to the actual point line of the
other coordinate. Both orientations use the actual diagonal-swap and
fixed-graph Picard identities.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerDiagonalMarkedRestriction

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerChowFunctional
open CurvePowerGraphRestrictions

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem letterClass_diagonal_swap (ambient : ℕ) (i j : Fin ambient) :
    letterClass k C c₀ ambient (.inr (i,j)) = letterClass k C c₀ ambient (.inr (j,i)) := by
  let e := CurvePowerGraphFixedRestrictions.swapTwo C
  have hm : reindex C ![i,j] ≫ e = reindex C ![j,i] := by
    change reindex C ![i,j] ≫ reindex C (Equiv.swap (0 : Fin 2) 1) = reindex C ![j,i]
    rw [reindex_comp]
    congr 1
    funext q
    fin_cases q <;> simp
  change Stacks.Picard.schemePullbackClass (reindex C ![i,j]).left (diagonalClass C) =
    Stacks.Picard.schemePullbackClass (reindex C ![j,i]).left (diagonalClass C)
  have hclass := congrArg (Stacks.Picard.schemePullbackClass (reindex C ![i,j]).left)
    (CurvePowerGraphFixedRestrictions.diagonalClass_pullback_swap C).symm
  have hcomp := Stacks.Picard.schemePullbackClass_comp (reindex C ![i,j]).left e.left
    (diagonalClass C)
  exact hclass.trans (hcomp.trans (congrArg (fun q : (power C ambient).left ⟶ (power C 2).left =>
    Stacks.Picard.schemePullbackClass q (diagonalClass C)) (congrArg Over.Hom.left hm)))

theorem diagonalClass_pullback_left_marked (ambient : ℕ) (s : State) (i j : Fin ambient)
    (hi : ∀ b ∈ s, b.testBit i.val = false) :
    Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
        (letterClass k C c₀ ambient (.inr (i,j))) =
      Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
        (letterClass k C c₀ ambient (.inl j)) := by
  let y : power C s.length ⟶ power C 1 := lift 1 (fun _ => stateCoordinate C c₀ s j.val)
  have hm : stateMap C c₀ ambient s ≫ reindex C ![i,j] =
      y ≫ graphOver C 1 (toUnit (power C 1) ≫ c₀) := by
    apply Stacks.CurvePower.hom_ext 2
    intro q
    fin_cases q
    · simp only [Category.assoc, reindex_coord, stateMap_coord]
      change stateCoordinate C c₀ s i.val =
        y ≫ graphOver C 1 (toUnit (power C 1) ≫ c₀) ≫ coord C 2 0
      rw [graphOver_coord_zero, stateCoordinate_eq_fixed C c₀ s i.val hi, ← Category.assoc]
      exact congrArg (fun g => g ≫ c₀) (toUnit_unique _ _)
    · simp only [Category.assoc, reindex_coord, stateMap_coord]
      change stateCoordinate C c₀ s j.val =
        y ≫ graphOver C 1 (toUnit (power C 1) ≫ c₀) ≫ coord C 2 (0 : Fin 1).succ
      rw [graphOver_coord_succ]
      exact (lift_coord 1 (fun _ => stateCoordinate C c₀ s j.val) 0).symm
  have hp : stateMap C c₀ ambient s ≫ reindex C (fun _ : Fin 1 => j) = y := by
    apply Stacks.CurvePower.hom_ext 1
    intro q
    simp only [Category.assoc, reindex_coord, stateMap_coord, y, lift_coord]
  have hd : Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
      (letterClass k C c₀ ambient (.inr (i,j))) =
      Stacks.Picard.schemePullbackClass y.left (pointClass C c₀) := by
    rw [letterClass, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, hm,
      Over.comp_left, ← Stacks.Picard.schemePullbackClass_comp]
    exact congrArg (Stacks.Picard.schemePullbackClass y.left)
      (CurvePowerGraphFixedRestrictions.diagonalClass_restrict_fixed C c₀)
  have hj : Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
      (letterClass k C c₀ ambient (.inl j)) =
      Stacks.Picard.schemePullbackClass y.left (pointClass C c₀) := by
    rw [letterClass, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, hp]
  exact hd.trans hj.symm

theorem diagonalClass_pullback_right_marked (ambient : ℕ) (s : State) (i j : Fin ambient)
    (hj : ∀ b ∈ s, b.testBit j.val = false) :
    Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
        (letterClass k C c₀ ambient (.inr (i,j))) =
      Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
        (letterClass k C c₀ ambient (.inl i)) :=
  (congrArg (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left)
    (letterClass_diagonal_swap k C c₀ ambient i j)).trans
      (diagonalClass_pullback_left_marked k C c₀ ambient s j i hj)

theorem tautologicalFunctional_diagonal_left_marked (ambient : ℕ) (s : State)
    (i j : Fin ambient) (tail : List (Letter ambient))
    (hi : ∀ b ∈ s, b.testBit i.val = false) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) s =
      tautologicalFunctional k C c₀ ambient (.inl j :: tail) s := by
  unfold tautologicalFunctional partitionFunctional
  simp only [List.map_cons]
  rw [diagonalClass_pullback_left_marked k C c₀ ambient s i j hi]

theorem tautologicalFunctional_diagonal_right_marked (ambient : ℕ) (s : State)
    (i j : Fin ambient) (tail : List (Letter ambient))
    (hj : ∀ b ∈ s, b.testBit j.val = false) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) s =
      tautologicalFunctional k C c₀ ambient (.inl i :: tail) s := by
  unfold tautologicalFunctional partitionFunctional
  simp only [List.map_cons]
  rw [diagonalClass_pullback_right_marked k C c₀ ambient s i j hj]

end M9Native.CurvePowerDiagonalMarkedRestriction

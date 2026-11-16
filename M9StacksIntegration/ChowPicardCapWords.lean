module

public import M9StacksIntegration.CurvePowerPointTrace

/-!
# Actual zero factors in Picard cap words

The zero Picard class acts by the actual zero first-Chern-cap map.
Consequently a marked point, or a diagonal with both vertices marked,
annihilates every remaining actual divisor word.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.ChowPicardCapWords

open Stacks.Chow CurveTopChowClass ChowCapWords CurvePowerChowFunctional
open CurvePowerGraphLocal

theorem wordDegree_cons_zero (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (xs : List (Stacks.Picard.ofScheme X)) :
    wordDegree k f ((0 :: xs).map chosenLine) = 0 := by
  let C := fieldChowSituation k
  let O := lineCap C f (chosenLine (0 : Stacks.Picard.ofScheme X))
  let Os := (xs.map chosenLine).map (lineCap C f)
  let a := identityChowClass C f (0 + ((O :: Os).length : ℤ))
  have hd : (0 : ℤ) + ((O :: Os).length : ℤ) = 0 + 1 + (Os.length : ℤ) := by
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring
  let b := chowGroupCast C f hd a
  have hz : O.capOnChow C f 0 = 0 := ChowPicardCap.capFun_zero C f 0
  change chowDegree C (fieldChowSituation_dimensionFunction_eq_zero k) f
    (IsLocalRing.closedPoint k) (iteratedChernCapOnChow C f (O :: Os) 0 a) = 0
  rw [iteratedChernCapOnChow_cons_eq C f O Os 0 a b
    (chowGroupCast_heq C f hd a).symm, hz]
  simp only [AddMonoidHom.zero_apply, map_zero]

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem tautologicalFunctional_cons_point_marked (ambient : ℕ)
    (i : Fin ambient) (tail : List (Letter ambient)) (s : State)
    (hi : ∀ b ∈ s, b.testBit i.val = false) :
    tautologicalFunctional k C c₀ ambient (.inl i :: tail) s = 0 := by
  unfold tautologicalFunctional partitionFunctional
  simp only [List.map_cons]
  rw [CurvePowerConstantClass.pointClass_pullback_marked k C c₀ ambient s i hi]
  simpa only [List.map_cons, List.map_map, Function.comp_def] using
    wordDegree_cons_zero k (power C s.length).hom
      (tail.map fun factor => Stacks.Picard.schemePullbackClass
        (CurvePowerGraphMaps.stateMap C c₀ ambient s).left (letterClass k C c₀ ambient factor))

theorem tautologicalFunctional_cons_diagonal_both_marked (ambient : ℕ)
    (i j : Fin ambient) (tail : List (Letter ambient)) (s : State)
    (hi : ∀ b ∈ s, b.testBit i.val = false)
    (hj : ∀ b ∈ s, b.testBit j.val = false) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) s = 0 := by
  unfold tautologicalFunctional partitionFunctional
  simp only [List.map_cons]
  rw [CurvePowerConstantClass.diagonalClass_pullback_both_marked k C c₀ ambient s i j hi hj]
  simpa only [List.map_cons, List.map_map, Function.comp_def] using
    wordDegree_cons_zero k (power C s.length).hom
      (tail.map fun factor => Stacks.Picard.schemePullbackClass
        (CurvePowerGraphMaps.stateMap C c₀ ambient s).left (letterClass k C c₀ ambient factor))

end M9Native.ChowPicardCapWords

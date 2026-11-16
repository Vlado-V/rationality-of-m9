module

public import M9StacksIntegration.CurvePowerDiagonalSelfClass
public import M9StacksIntegration.CurvePowerPointWordDegree

/-!
# Actual self-diagonal restriction against every remaining word

The coefficient is the degree of the actual self-diagonal line on the
actual first curve power. The genuine curve-degree word comparison
replaces its pullback by that coefficient times the actual point line.
The already-proved point restriction then pins the original block.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerDiagonalSelfRestriction

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerGraphMapReindex
open CurvePowerChowFunctional CurvePowerGraphRestrictions

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

def selfDegree : ℤ :=
  invertibleCurveDegreeHom k (power C 1).hom
    (CurvePowerPointWordDegree.power_one_dim k C hC).le
    (Stacks.Picard.schemePullbackClass (reindex C ![(0 : Fin 1),0]).left
      (CurvePowerGraphCartier.graphClass C 1 (coord C 1 0)))

include hC

theorem tautologicalFunctional_diagonal_same_head (ambient b : ℕ) (s : State)
    (i j : Fin ambient) (tail : List (Letter ambient))
    (hi : b.testBit i.val = true) (hj : b.testBit j.val = true)
    (hsep : Separated (b :: s)) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) (b :: s) =
      selfDegree k C hC * tautologicalFunctional k C c₀ ambient tail s := by
  let S := Stacks.Picard.schemePullbackClass (reindex C ![(0 : Fin 1),0]).left
    (CurvePowerGraphCartier.graphClass C 1 (coord C 1 0))
  let P := CurvePowerGraphCartier.graphClass C 0 c₀
  let g := (firstMap C s.length).left
  let xs : List (Stacks.Picard.ofScheme (power C (s.length + 1)).left) :=
    tail.map fun factor => Stacks.Picard.schemePullbackClass
      (stateMap C c₀ ambient (b :: s)).left (letterClass k C c₀ ambient factor)
  have hl : tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) (b :: s) =
      wordDegree k (power C (s.length + 1)).hom
        ((Stacks.Picard.schemePullbackClass g S :: xs).map chosenLine) := by
    unfold tautologicalFunctional partitionFunctional
    simp only [List.map_cons]
    rw [CurvePowerDiagonalSelfClass.diagonalClass_pullback_same_head
      k C c₀ ambient b s i j hi hj]
    simp only [List.length_cons, List.map_map, Function.comp_def, xs, S, g]
  let := CurvePowerDiagonalSelfClass.isProper_power_map k C (firstMap C s.length)
  have hr := CurvePowerPointWordDegree.wordDegree_pullback_point k C c₀ hC
    (power C (s.length + 1)).hom g (Over.w (firstMap C s.length)) S xs
  let D := CurvePowerGraphCartier.graphClass C s.length (toUnit (power C s.length) ≫ c₀)
  have hd : Stacks.Picard.schemePullbackClass g P = D :=
    (constant_graphClass C c₀ s.length).symm
  have hw := congrArg (fun x : Stacks.Picard.ofScheme (power C (s.length + 1)).left =>
    wordDegree k (power C (s.length + 1)).hom ((x :: xs).map chosenLine)) hd
  have hp : tautologicalFunctional k C c₀ ambient (.inl i :: tail) (b :: s) =
      wordDegree k (power C (s.length + 1)).hom ((D :: xs).map chosenLine) := by
    unfold tautologicalFunctional partitionFunctional
    simp only [List.map_cons]
    rw [CurvePowerPointRestriction.pointClass_pullback_head k C c₀ ambient b s i hi]
    simp only [List.length_cons, List.map_map, Function.comp_def, xs, D]
  have ht := CurvePowerPointRestriction.tautologicalFunctional_point_head
    k C c₀ hC ambient b s i tail hi hsep
  have hpoint := hw.trans (hp.symm.trans ht)
  exact hl.trans (hr.trans (congrArg (fun z => selfDegree k C hC * z) hpoint))

theorem tautologicalFunctional_diagonal_same_block (ambient : ℕ) (i j : Fin ambient)
    (tail : List (Letter ambient)) (s : State) (hs : s.Nodup) (hsep : Separated s)
    (b : ℕ) (hb : b ∈ s) (hi : b.testBit i.val = true) (hj : b.testBit j.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) s =
      selfDegree k C hC * tautologicalFunctional k C c₀ ambient tail (s.erase b) := by
  have hp : s.Perm (b :: s.erase b) := List.perm_cons_erase hb
  have ht : (b :: s.erase b).Nodup := hp.nodup_iff.mp hs
  let e := indexEquiv s (b :: s.erase b) hs ht hp
  have hst : Separated (b :: s.erase b) :=
    separated_of_index_equiv s _ hsep e (get_indexEquiv s _ hs ht hp)
  have hv := CurvePowerPairingReindex.partitionFunctional_state_perm k C c₀ ambient
    ((.inr (i,j) :: tail).map (letterClass k C c₀ ambient)) s (b :: s.erase b) hs ht hsep hp
  exact hv.trans (tautologicalFunctional_diagonal_same_head k C c₀ hC
    ambient b (s.erase b) i j tail hi hj hst)

end M9Native.CurvePowerDiagonalSelfRestriction

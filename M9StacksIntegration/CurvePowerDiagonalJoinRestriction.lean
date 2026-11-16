module

public import M9StacksIntegration.CurvePowerPointRestriction
public import M9StacksIntegration.CurvePowerGraphDisjoint

/-!
# Actual diagonal restriction joining two free partition blocks

The original coordinate graph is the actual coordinate-doubling map.
Its cap joins the two original blocks by their literal bitwise union.
An actual finite permutation brings any chosen distinct blocks to those
first two coordinates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerDiagonalJoinRestriction

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerGraphMapRestrictions
open CurvePowerGraphMapReindex CurvePowerGraphBlockRestriction CurvePowerChowFunctional
open CurvePowerGraphDisjoint

section Maps

variable {S : Scheme.{u}} (C : Over S) (c₀ : power C 0 ⟶ C)

theorem coordinateGraph_eq_duplicateFirst (m : ℕ) :
    Stacks.Hilbert.pointGraph C (power C (m + 1)) (coord C (m + 1) 0) =
      (duplicateFirst C m).left := by
  refine pullback.hom_ext ?_ ?_
  · change _ = (duplicateFirst C m ≫ fst C (power C (m + 1))).left
    rw [duplicateFirst_fst]
    exact Stacks.Hilbert.pointGraph_comp_fst C (power C (m + 1)) _
  · change _ = (duplicateFirst C m ≫ snd C (power C (m + 1))).left
    rw [duplicateFirst_snd]
    exact Stacks.Hilbert.pointGraph_comp_snd C (power C (m + 1)) _

theorem coordinateGraph_stateMap (ambient a b : ℕ) (s : State) :
    Stacks.Hilbert.pointGraph C (power C (s.length + 1)) (coord C (s.length + 1) 0) ≫
        (stateMap C c₀ ambient (a :: b :: s)).left =
      (stateMap C c₀ ambient ((a ||| b) :: s)).left := by
  exact (congrArg (fun g => g ≫ (stateMap C c₀ ambient (a :: b :: s)).left)
    (coordinateGraph_eq_duplicateFirst C s.length)).trans
      (congrArg Over.Hom.left (duplicateFirst_stateMap C c₀ ambient a b s))

end Maps

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

omit [IsAlgClosed k] in
theorem diagonalClass_pullback_head (ambient a b : ℕ) (s : State) (i j : Fin ambient)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (haj : a.testBit j.val = false) :
    Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient (a :: b :: s)).left
        (letterClass k C c₀ ambient (.inr (i,j))) =
      CurvePowerGraphCartier.graphClass C (s.length + 1) (coord C (s.length + 1) 0) := by
  have hm : stateMap C c₀ ambient (a :: b :: s) ≫ reindex C ![i,j] =
      reindex C (CurvePowerGraphBaseChange.extendIndex
        (fun _ : Fin 1 => (0 : Fin (s.length + 1)))) := by
    apply Stacks.CurvePower.hom_ext 2
    intro q
    rw [Category.assoc, reindex_coord, reindex_coord, stateMap_coord]
    fin_cases q
    · exact stateCoordinate_cons_of_mem C c₀ a (b :: s) i.val hi
    · change stateCoordinate C c₀ (a :: b :: s) j.val =
        snd C (power C (s.length + 1)) ≫ fst C (power C s.length)
      rw [stateCoordinate_cons_of_not_mem C c₀ a (b :: s) j.val haj,
        stateCoordinate_cons_of_mem C c₀ b s j.val hj]
      simp only [List.length_cons]
  rw [letterClass, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, hm]
  exact (CurvePowerGraphRestrictions.coordinate_graphClass C (s.length + 1) 0).symm

include hC

theorem tautologicalFunctional_diagonal_head (ambient a b : ℕ) (s : State)
    (i j : Fin ambient) (tail : List (Letter ambient))
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (haj : a.testBit j.val = false) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) (a :: b :: s) =
      tautologicalFunctional k C c₀ ambient tail ((a ||| b) :: s) := by
  let D := CurvePowerGraphCartier.graphClass C (s.length + 1) (coord C (s.length + 1) 0)
  let xs : List (Stacks.Picard.ofScheme (power C (s.length + 2)).left) :=
    tail.map fun factor => Stacks.Picard.schemePullbackClass
      (stateMap C c₀ ambient (a :: b :: s)).left (letterClass k C c₀ ambient factor)
  have hl : tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) (a :: b :: s) =
      wordDegree k (power C (s.length + 2)).hom ((D :: xs).map chosenLine) := by
    unfold tautologicalFunctional partitionFunctional
    simp only [List.map_cons]
    rw [diagonalClass_pullback_head k C c₀ ambient a b s i j hi hj haj]
    simp only [List.length_cons, List.map_map, Function.comp_def, xs, D]
  have hp : wordDegree k (power C (s.length + 2)).hom ((D :: xs).map chosenLine) =
      wordDegree k (power C (s.length + 2)).hom ((xs ++ [D]).map chosenLine) :=
    wordDegree_perm k _ ((List.perm_append_comm (l₁ := [D]) (l₂ := xs)).map chosenLine)
  have hr := CurvePowerGraphCapPairing.wordDegree_append_graph k C hC (s.length + 1)
    (coord C (s.length + 1) 0) xs
  let g := Stacks.Hilbert.pointGraph C (power C (s.length + 1)) (coord C (s.length + 1) 0)
  have hm := coordinateGraph_stateMap C c₀ ambient a b s
  have hclass (x : LineClass C ambient) :
      Stacks.Picard.schemePullbackClass g
        (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient (a :: b :: s)).left x) =
      Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient ((a ||| b) :: s)).left x := by
    have hh := Stacks.Picard.schemePullbackClass_comp g
      (stateMap C c₀ ambient (a :: b :: s)).left x
    exact hh.trans (congrArg (fun q : (power C (s.length + 1)).left ⟶ (power C ambient).left =>
      Stacks.Picard.schemePullbackClass q x) hm)
  have hx : xs.map (Stacks.Picard.schemePullbackClass g) =
      tail.map (fun factor => Stacks.Picard.schemePullbackClass
        (stateMap C c₀ ambient ((a ||| b) :: s)).left (letterClass k C c₀ ambient factor)) := by
    dsimp only [xs]
    rw [List.map_map]
    apply List.map_congr_left
    intro factor _
    exact hclass (letterClass k C c₀ ambient factor)
  have hw := congrArg (fun ws => wordDegree k (power C (s.length + 1)).hom
    (ws.map chosenLine)) hx
  simpa only [tautologicalFunctional, partitionFunctional, List.length_cons,
    List.map_map, Function.comp_def] using
    hl.trans (hp.trans (hr.trans hw))

theorem tautologicalFunctional_diagonal_free_blocks (ambient : ℕ) (i j : Fin ambient)
    (tail : List (Letter ambient)) (s : State) (hs : s.Nodup) (hsep : Separated s)
    (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) s =
      tautologicalFunctional k C c₀ ambient tail ((a ||| b) :: (s.erase a).erase b) := by
  have hbt : b ∈ s.erase a := (List.mem_erase_of_ne (Ne.symm hab)).mpr hb
  have hp : s.Perm (a :: b :: (s.erase a).erase b) :=
    (List.perm_cons_erase ha).trans ((List.perm_cons_erase hbt).cons a)
  have ht : (a :: b :: (s.erase a).erase b).Nodup := hp.nodup_iff.mp hs
  let e := indexEquiv s _ hs ht hp
  have hst : Separated (a :: b :: (s.erase a).erase b) :=
    separated_of_index_equiv s _ hsep e (get_indexEquiv s _ hs ht hp)
  have haj : a.testBit j.val = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh := separated_cons_disjoint a (b :: (s.erase a).erase b) hst j.val h b
      (List.mem_cons_self)
    exact Bool.noConfusion (hj.symm.trans hh)
  have hv := CurvePowerPairingReindex.partitionFunctional_state_perm k C c₀ ambient
    ((.inr (i,j) :: tail).map (letterClass k C c₀ ambient)) s _ hs ht hsep hp
  exact hv.trans (tautologicalFunctional_diagonal_head k C c₀ hC ambient a b
    ((s.erase a).erase b) i j tail hi hj haj)

end M9Native.CurvePowerDiagonalJoinRestriction

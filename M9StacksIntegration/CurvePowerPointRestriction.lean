module

public import M9StacksIntegration.CurvePowerGraphCapPairing
public import M9StacksIntegration.CurvePowerPairingReindex
public import M9StacksIntegration.ChowPicardCapWords

/-!
# Actual point restriction for a separated partition

An actual free block is moved to the first coordinate by its constructed
finite permutation. The actual point graph restricts the remaining
word to the partition with that block removed. A marked vertex acts by
the actual zero Picard cap.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerPointRestriction

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerGraphMapRestrictions
open CurvePowerGraphMapReindex CurvePowerGraphBlockRestriction CurvePowerChowFunctional

theorem blockAt_mem_and_testBit (v : ℕ) (s : State) (h : blockAt v s ≠ 0) :
    blockAt v s ∈ s ∧ (blockAt v s).testBit v = true := by
  induction s with
  | nil => exact (h rfl).elim
  | cons a s ih =>
      cases ha : a.testBit v with
      | false =>
          have hh : blockAt v s ≠ 0 := by simpa only [blockAt, ha, Bool.false_eq_true, ite_false] using h
          have ht := ih hh
          simpa only [blockAt, ha, Bool.false_eq_true, ite_false] using
            And.intro (List.mem_cons_of_mem a ht.1) ht.2
      | true =>
          simpa only [blockAt, ha, ite_true] using
            And.intro (List.mem_cons_self : a ∈ a :: s) ha

theorem blockAt_eq_zero_iff (v : ℕ) (s : State) :
    blockAt v s = 0 ↔ ∀ a ∈ s, a.testBit v = false := by
  induction s with
  | nil => simp [blockAt]
  | cons a s ih =>
      cases ha : a.testBit v with
      | false => simpa only [blockAt, ha, Bool.false_eq_true, ite_false,
          List.forall_mem_cons, true_and] using ih
      | true =>
          have hz : a ≠ 0 := by
            intro h
            subst a
            simp at ha
          simp only [blockAt, ha, ite_true, hz, List.forall_mem_cons,
            Bool.true_eq_false, false_and]

section Maps

variable {S : Scheme.{u}} (C : Over S) (c₀ : power C 0 ⟶ C)

theorem constantGraph_eq_insertZero (m : ℕ) :
    Stacks.Hilbert.pointGraph C (power C m) (toUnit (power C m) ≫ c₀) =
      (insertConstant C c₀ m 0).left := by
  refine pullback.hom_ext ?_ ?_
  · change _ = (insertConstant C c₀ m 0 ≫ fst C (power C m)).left
    rw [insertConstant_zero_fst]
    exact Stacks.Hilbert.pointGraph_comp_fst C (power C m) _
  · change _ = (insertConstant C c₀ m 0 ≫ snd C (power C m)).left
    rw [insertConstant_zero_snd]
    exact Stacks.Hilbert.pointGraph_comp_snd C (power C m) _

theorem constantGraph_stateMap (ambient b : ℕ) (s : State) (hsep : Separated (b :: s)) :
    Stacks.Hilbert.pointGraph C (power C s.length) (toUnit (power C s.length) ≫ c₀) ≫
        (stateMap C c₀ ambient (b :: s)).left = (stateMap C c₀ ambient s).left := by
  have hm := insertConstant_stateMap C c₀ ambient b s
    (fun i hi => separated_cons_disjoint b s hsep i.val hi)
  exact (congrArg (fun g => g ≫ (stateMap C c₀ ambient (b :: s)).left)
    (constantGraph_eq_insertZero C c₀ s.length)).trans
      (congrArg Over.Hom.left hm)

end Maps

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

omit [IsAlgClosed k] in
theorem pointClass_pullback_head (ambient b : ℕ) (s : State) (i : Fin ambient)
    (hi : b.testBit i.val = true) :
    Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient (b :: s)).left
        (letterClass k C c₀ ambient (.inl i)) =
      CurvePowerGraphCartier.graphClass C s.length (toUnit (power C s.length) ≫ c₀) := by
  have hm : stateMap C c₀ ambient (b :: s) ≫ reindex C (fun _ : Fin 1 => i) =
      CurvePowerGraphRestrictions.firstMap C s.length := by
    apply Stacks.CurvePower.hom_ext 1
    intro a
    simp only [Category.assoc, reindex_coord, stateMap_coord]
    exact stateCoordinate_cons_of_mem C c₀ b s i.val hi
  rw [letterClass, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, hm]
  exact (CurvePowerGraphRestrictions.constant_graphClass C c₀ s.length).symm

include hC

theorem tautologicalFunctional_point_head (ambient b : ℕ) (s : State)
    (i : Fin ambient) (tail : List (Letter ambient))
    (hi : b.testBit i.val = true) (hsep : Separated (b :: s)) :
    tautologicalFunctional k C c₀ ambient (.inl i :: tail) (b :: s) =
      tautologicalFunctional k C c₀ ambient tail s := by
  let D := CurvePowerGraphCartier.graphClass C s.length (toUnit (power C s.length) ≫ c₀)
  let xs : List (Stacks.Picard.ofScheme (power C (s.length + 1)).left) :=
    tail.map fun factor => Stacks.Picard.schemePullbackClass
      (stateMap C c₀ ambient (b :: s)).left (letterClass k C c₀ ambient factor)
  have hl : tautologicalFunctional k C c₀ ambient (.inl i :: tail) (b :: s) =
      wordDegree k (power C (s.length + 1)).hom ((D :: xs).map chosenLine) := by
    unfold tautologicalFunctional partitionFunctional
    simp only [List.map_cons]
    rw [pointClass_pullback_head k C c₀ ambient b s i hi]
    simp only [List.length_cons, List.map_map, Function.comp_def, xs, D]
  have hperm : wordDegree k (power C (s.length + 1)).hom ((D :: xs).map chosenLine) =
      wordDegree k (power C (s.length + 1)).hom ((xs ++ [D]).map chosenLine) :=
    wordDegree_perm k _ ((List.perm_append_comm (l₁ := [D]) (l₂ := xs)).map chosenLine)
  have hr := CurvePowerGraphCapPairing.wordDegree_append_graph k C hC s.length
    (toUnit (power C s.length) ≫ c₀) xs
  let g := Stacks.Hilbert.pointGraph C (power C s.length) (toUnit (power C s.length) ≫ c₀)
  have hm := constantGraph_stateMap C c₀ ambient b s hsep
  have hp (x : LineClass C ambient) :
      Stacks.Picard.schemePullbackClass g
        (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient (b :: s)).left x) =
      Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left x := by
    have hh := Stacks.Picard.schemePullbackClass_comp g
      (stateMap C c₀ ambient (b :: s)).left x
    exact hh.trans (congrArg (fun q : (power C s.length).left ⟶ (power C ambient).left =>
      Stacks.Picard.schemePullbackClass q x) hm)
  have hx : xs.map (Stacks.Picard.schemePullbackClass g) =
      tail.map (fun factor => Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
        (letterClass k C c₀ ambient factor)) := by
    dsimp only [xs]
    rw [List.map_map]
    apply List.map_congr_left
    intro factor _
    exact hp (letterClass k C c₀ ambient factor)
  have hw := congrArg (fun ws => wordDegree k (power C s.length).hom (ws.map chosenLine)) hx
  simpa only [tautologicalFunctional, partitionFunctional, List.map_map, Function.comp_def] using
    hl.trans (hperm.trans (hr.trans hw))

theorem tautologicalFunctional_point_free_block (ambient : ℕ) (i : Fin ambient)
    (tail : List (Letter ambient)) (s : State) (hs : s.Nodup) (hsep : Separated s)
    (b : ℕ) (hb : b ∈ s) (hi : b.testBit i.val = true) :
    tautologicalFunctional k C c₀ ambient (.inl i :: tail) s =
      tautologicalFunctional k C c₀ ambient tail (s.erase b) := by
  have hp : s.Perm (b :: s.erase b) := List.perm_cons_erase hb
  have ht : (b :: s.erase b).Nodup := hp.nodup_iff.mp hs
  let e := indexEquiv s (b :: s.erase b) hs ht hp
  have hst : Separated (b :: s.erase b) :=
    separated_of_index_equiv s _ hsep e (get_indexEquiv s _ hs ht hp)
  have hv := CurvePowerPairingReindex.partitionFunctional_state_perm k C c₀ ambient
    ((.inl i :: tail).map (letterClass k C c₀ ambient)) s (b :: s.erase b) hs ht hsep hp
  exact hv.trans (tautologicalFunctional_point_head k C c₀ hC ambient b (s.erase b) i tail hi hst)

theorem tautologicalFunctional_point_step (ambient : ℕ) (i : Fin ambient)
    (tail : List (Letter ambient)) (s : State) (hs : s.Nodup) (hsep : Separated s) :
    tautologicalFunctional k C c₀ ambient (.inl i :: tail) s =
      match pointStep i.val s with
      | none => 0
      | some s' => tautologicalFunctional k C c₀ ambient tail s' := by
  by_cases hb : blockAt i.val s = 0
  · simp only [pointStep, hb, ite_true]
    exact ChowPicardCapWords.tautologicalFunctional_cons_point_marked k C c₀ ambient i tail s
      ((blockAt_eq_zero_iff i.val s).mp hb)
  · have hh := blockAt_mem_and_testBit i.val s hb
    simp only [pointStep, hb, ite_false]
    exact tautologicalFunctional_point_free_block k C c₀ hC ambient i tail s hs hsep
      (blockAt i.val s) hh.1 hh.2

end M9Native.CurvePowerPointRestriction

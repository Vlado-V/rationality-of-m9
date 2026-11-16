module

public import M9StacksIntegration.CurvePowerPointRestriction
public import M9StacksIntegration.CurvePowerGraphContextStepTransport
public import M9StacksIntegration.CurvePowerGraphKeyInduction

/-!
# Actual point restriction of the transported modified diagonal

The functional is the literal native Chow-cap functional. Its point
restriction is proved by the actual partition pointStep rule and the
proved disjoint-context step transport. Selection of outside labels is
an actual finite-list reframe preserving the same seven cycle terms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGammaPoint

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphDisjoint
open CurvePowerGraphInduction CurvePowerGraphContextSelection
open CurvePowerChowFunctional

abbrev AdmissibleFrame := {ctx : Context // Admissible ctx}

def selectedFrame (frame : AdmissibleFrame) (v w : ℕ) : AdmissibleFrame :=
  ⟨selectPair frame.val v w, selectPair_admissible frame.val frame.property v w⟩

theorem realization_pointAction_of_rule (t : ℤ) (A B : State → ℤ) (i : ℕ)
    (c : SourceCombination)
    (h : ∀ s ∈ c.map Prod.fst, A s = match pointStep i s with
      | none => 0
      | some s' => B s') :
    realization t A (embed c) = realization t B (pointAction i c) := by
  induction c with
  | nil => simp only [embed, List.map_nil, pointAction, List.flatMap_nil, realization_nil]
  | cons p c ih =>
      rcases p with ⟨s,a⟩
      have hs := h s (by simp)
      have hc : ∀ q ∈ c.map Prod.fst, A q = match pointStep i q with
          | none => 0
          | some q' => B q' := by
        intro q hq
        exact h q (by simp [hq])
      have ht := ih hc
      cases hp : pointStep i s with
      | none =>
          have hs0 : A s = 0 := by simpa only [hp] using hs
          simpa only [embed, List.map_cons, pointAction, List.flatMap_cons, hp,
            List.nil_append, realization_cons, zero_mul, add_zero, hs0, smul_zero,
            zero_add] using ht
      | some s' =>
          have hs' : A s = B s' := by simpa only [hp] using hs
          simpa only [embed, List.map_cons, pointAction, List.flatMap_cons, hp,
            List.singleton_append, realization_cons, zero_mul, add_zero, hs'] using
              congrArg (fun z => a • B s' + z) ht

theorem transport_marked (ctx : Context) (v : ℕ)
    (hl : ∀ i : Fin 5, (ctx.label i).testBit v = false)
    (hs : ∀ a ∈ ctx.spectator, a.testBit v = false)
    (s : State) : ∀ a ∈ transport ctx s, a.testBit v = false := by
  intro a ha
  have hm := (canonical_perm _).subset ha
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hm).1
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨i, _, hi⟩ := (liftMask_testBit_iff ctx.label b v).mp h
    exact Bool.noConfusion ((hl i).symm.trans hi)
  · exact hs a hm

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

def actualFunctional (ambient : ℕ) : Functional AdmissibleFrame (Letter ambient) ℤ :=
  fun frame word s => tautologicalFunctional k C c₀ ambient word (transport frame.val s)

theorem gammaValue_selectedFrame (t : ℤ) (ambient : ℕ) (frame : AdmissibleFrame)
    (v w : ℕ) (word : List (Letter ambient)) :
    gammaValue t (actualFunctional k C c₀ ambient) frame word =
      gammaValue t (actualFunctional k C c₀ ambient) (selectedFrame frame v w) word := by
  change realization t (tautologicalFunctional k C c₀ ambient word ∘ transport frame.val)
      (embed localGamma) =
    realization t (tautologicalFunctional k C c₀ ambient word ∘
      transport (selectPair frame.val v w)) (embed localGamma)
  exact CurvePowerGraphReframe.realization_localGamma_of_outside_perm t
    (tautologicalFunctional k C c₀ ambient word) frame.val (selectPair frame.val v w)
    (selectPair_special frame.val v w 0 (by decide)).symm
    (selectPair_special frame.val v w 1 (by decide)).symm
    (selectPair_special frame.val v w 2 (by decide)).symm
    (selectPair_outside_perm frame.val frame.property v w)

theorem gammaValue_point_marked (t : ℤ) (ambient : ℕ) (frame : AdmissibleFrame)
    (v : Fin ambient) (tail : List (Letter ambient))
    (hl : ∀ i : Fin 5, (frame.val.label i).testBit v.val = false)
    (hs : ∀ a ∈ frame.val.spectator, a.testBit v.val = false) :
    gammaValue t (actualFunctional k C c₀ ambient) frame (.inl v :: tail) = 0 := by
  apply realization_zero_of_keys
  intro s _
  exact ChowPicardCapWords.tautologicalFunctional_cons_point_marked k C c₀ ambient v tail
    (transport frame.val s) (transport_marked frame.val v.val hl hs s)

theorem gammaValue_point_restriction [IsAlgClosed k] [IsVariety k C.hom]
    (hC : topologicalKrullDim C.left = 1) (t : ℤ) (ambient : ℕ)
    (frame : AdmissibleFrame) (i : Fin 5) (v : Fin ambient)
    (hi : (frame.val.label i).testBit v.val = true) (tail : List (Letter ambient)) :
    gammaValue t (actualFunctional k C c₀ ambient) frame (.inl v :: tail) =
      realization t (tautologicalFunctional k C c₀ ambient tail ∘ transport frame.val)
        (pointAction i.val localGamma) := by
  apply realization_pointAction_of_rule
  intro s hs
  have hsk : s ∈ keys (embed localGamma) := by
    simpa only [keys, embed, List.map_map, Function.comp_def] using hs
  have hp := transported_localGamma_actual_map_properties frame.val frame.property.2 s hsk
  have hv := CurvePowerPointRestriction.tautologicalFunctional_point_step k C c₀ hC
    ambient v tail (transport frame.val s) hp.1 hp.2
  rw [CurvePowerGraphContextStepTransport.pointStep_transport frame.val frame.property i
    v.val hi s hsk] at hv
  cases hs' : pointStep i.val s <;>
    simpa only [hs', Option.map_none, Option.map_some, Function.comp_apply, actualFunctional] using hv

end M9Native.CurvePowerGammaPoint

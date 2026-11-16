module

public import M9StacksIntegration.CurvePowerDiagonalRestriction
public import M9StacksIntegration.CurvePowerGammaPoint

/-!
# Actual diagonal restriction of the transported modified diagonal

The repeated-block coefficient is the degree of the actual self line.
Every local loop flag is preserved by the proved context transport,
and the restriction is supplied by the actual native diagonalStep.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGammaDiagonal

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphDisjoint
open CurvePowerGraphInduction CurvePowerChowFunctional CurvePowerGammaPoint
open CurvePowerDiagonalSelfRestriction

theorem realization_diagonalAction_of_rule (t : ℤ) (A B : State → ℤ) (i j : ℕ)
    (c : SourceCombination)
    (h : ∀ s ∈ c.map Prod.fst, A s = match diagonalStep i j s with
      | none => 0
      | some (s', loop) => if loop then t * B s' else B s') :
    realization t A (embed c) = realization t B (diagonalAction i j c) := by
  induction c with
  | nil => simp only [embed, List.map_nil, diagonalAction, List.flatMap_nil, realization_nil]
  | cons p c ih =>
      rcases p with ⟨s,a⟩
      have hs := h s (by simp)
      have hc : ∀ q ∈ c.map Prod.fst, A q = match diagonalStep i j q with
          | none => 0
          | some (q', loop) => if loop then t * B q' else B q' := by
        intro q hq
        exact h q (by simp [hq])
      have ht := ih hc
      cases hp : diagonalStep i j s with
      | none =>
          have hs0 : A s = 0 := by simpa only [hp] using hs
          simpa only [embed, List.map_cons, diagonalAction, List.flatMap_cons, hp,
            List.nil_append, realization_cons, zero_mul, add_zero, hs0, smul_zero,
            zero_add] using ht
      | some p' =>
          rcases p' with ⟨s',loop⟩
          cases loop with
          | false =>
              have hs' : A s = B s' := by simpa only [hp, Bool.false_eq_true, ite_false] using hs
              simpa only [embed, List.map_cons, diagonalAction, List.flatMap_cons, hp,
                Bool.false_eq_true, ite_false,
                List.singleton_append, realization_cons, zero_mul, add_zero, hs'] using
                  congrArg (fun z => a • B s' + z) ht
          | true =>
              have hs' : A s = t * B s' := by simpa only [hp, ite_true] using hs
              simpa only [embed, List.map_cons, diagonalAction, List.flatMap_cons, hp,
                List.singleton_append, realization_cons, ite_true, zero_mul, mul_zero, add_zero,
                zero_add, hs', smul_eq_mul, mul_assoc] using
                  congrArg (fun z => (a * t) * B s' + z) ht

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

omit [IsAlgClosed k] [IsVariety k C.hom] in
theorem gammaValue_diagonal_left_marked (t : ℤ) (ambient : ℕ) (frame : AdmissibleFrame)
    (v w : Fin ambient) (tail : List (Letter ambient))
    (hl : ∀ i : Fin 5, (frame.val.label i).testBit v.val = false)
    (hs : ∀ a ∈ frame.val.spectator, a.testBit v.val = false) :
    gammaValue t (actualFunctional k C c₀ ambient) frame (.inr (v,w) :: tail) =
      gammaValue t (actualFunctional k C c₀ ambient) frame (.inl w :: tail) := by
  rw [gammaValue, gammaValue, realization_embed, realization_embed]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rcases p with ⟨s,a⟩
  have h := CurvePowerDiagonalMarkedRestriction.tautologicalFunctional_diagonal_left_marked
    k C c₀ ambient (transport frame.val s) v w tail (transport_marked frame.val v.val hl hs s)
  simpa only [actualFunctional] using congrArg (fun z => a • z) h

omit [IsAlgClosed k] [IsVariety k C.hom] in
theorem gammaValue_diagonal_right_marked (t : ℤ) (ambient : ℕ) (frame : AdmissibleFrame)
    (v w : Fin ambient) (tail : List (Letter ambient))
    (hl : ∀ i : Fin 5, (frame.val.label i).testBit w.val = false)
    (hs : ∀ a ∈ frame.val.spectator, a.testBit w.val = false) :
    gammaValue t (actualFunctional k C c₀ ambient) frame (.inr (v,w) :: tail) =
      gammaValue t (actualFunctional k C c₀ ambient) frame (.inl v :: tail) := by
  rw [gammaValue, gammaValue, realization_embed, realization_embed]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rcases p with ⟨s,a⟩
  have h := CurvePowerDiagonalMarkedRestriction.tautologicalFunctional_diagonal_right_marked
    k C c₀ ambient (transport frame.val s) v w tail (transport_marked frame.val w.val hl hs s)
  simpa only [actualFunctional] using congrArg (fun z => a • z) h

theorem gammaValue_diagonal_restriction (hC : topologicalKrullDim C.left = 1)
    (ambient : ℕ) (frame : AdmissibleFrame) (i j : Fin 5) (v w : Fin ambient)
    (hi : (frame.val.label i).testBit v.val = true)
    (hj : (frame.val.label j).testBit w.val = true) (tail : List (Letter ambient)) :
    gammaValue (selfDegree k C hC) (actualFunctional k C c₀ ambient) frame
        (.inr (v,w) :: tail) =
      realization (selfDegree k C hC)
        (tautologicalFunctional k C c₀ ambient tail ∘ transport frame.val)
        (diagonalAction i.val j.val localGamma) := by
  apply realization_diagonalAction_of_rule
  intro s hs
  have hsk : s ∈ keys (embed localGamma) := by
    simpa only [keys, embed, List.map_map, Function.comp_def] using hs
  have hp := transport_pairwise frame.val frame.property.2 s (localGamma_pairwise s hsk)
  have hn := transport_nonzero frame.val frame.property.2 s
  have hv := CurvePowerDiagonalRestriction.tautologicalFunctional_diagonal_step k C c₀ hC
    ambient v w tail (transport frame.val s) hp hn
  rw [CurvePowerGraphContextStepTransport.diagonalStep_transport frame.val frame.property
    i j v.val w.val hi hj s hsk] at hv
  cases hs' : diagonalStep i.val j.val s with
  | none =>
      simpa only [hs', Option.map_none, Function.comp_apply, actualFunctional] using hv
  | some p =>
      rcases p with ⟨s',loop⟩
      simpa only [hs', Option.map_some, Function.comp_apply, actualFunctional] using hv

end M9Native.CurvePowerGammaDiagonal

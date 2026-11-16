module

public import M9StacksIntegration.CurvePowerGammaPoint

/-! The literal three-block frame and its seven transported states.
This construction uses only disjoint nonzero masks; it supplies no
geometric intersection identity or vanishing law. -/

@[expose] public noncomputable section
set_option maxRecDepth 4096

namespace M9Native.CurvePowerThreeBlockContext

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphDisjoint
open CurvePowerGraphContextValidity CurvePowerGraphReframe CurvePowerGraphInduction

/-- The two unused local labels are absent; every untouched block stays
in the spectator list. -/
def context (a b c : ℕ) (spectator : State) : Context where
  label := ![a, b, c, 0, 0]
  spectator := spectator

/-- Disjoint nonzero actual blocks give the exact admissibility required
by the genuine transported modified-diagonal construction. -/
theorem admissible (a b c : ℕ) (spectator : State)
    (hpair : (a :: b :: c :: spectator).Pairwise MaskDisjoint)
    (hnonzero : ∀ x ∈ a :: b :: c :: spectator, x ≠ 0) :
    Admissible (context a b c spectator) := by
  obtain ⟨ha, hpbc⟩ := List.pairwise_cons.mp hpair
  obtain ⟨hb, hpcs⟩ := List.pairwise_cons.mp hpbc
  obtain ⟨hc, hps⟩ := List.pairwise_cons.mp hpcs
  have hab : MaskDisjoint a b := ha b (by simp)
  have hac : MaskDisjoint a c := ha c (by simp)
  have hbc : MaskDisjoint b c := hb c (by simp)
  constructor
  · exact ⟨hnonzero a (by simp), hnonzero b (by simp), hnonzero c (by simp)⟩
  · refine ⟨?_, hps, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [context, MaskDisjoint] at hij ⊢
      all_goals first
        | exact hab
        | exact hac
        | exact hbc
        | exact maskDisjoint_symm hab
        | exact maskDisjoint_symm hac
        | exact maskDisjoint_symm hbc
    · intro i x hx
      change x ∈ spectator at hx
      fin_cases i
      · exact ha x (by simp [hx])
      · exact hb x (by simp [hx])
      · exact hc x hx
      · simp [context, MaskDisjoint]
      · simp [context, MaskDisjoint]
    · intro x hx
      change x ∈ spectator at hx
      exact hnonzero x (by simp [hx])

/-- The actual admissible-frame subtype, with the literal labels and spectators. -/
def frame (a b c : ℕ) (spectator : State)
    (hpair : (a :: b :: c :: spectator).Pairwise MaskDisjoint)
    (hnonzero : ∀ x ∈ a :: b :: c :: spectator, x ≠ 0) :
    CurvePowerGammaPoint.AdmissibleFrame :=
  ⟨context a b c spectator, admissible a b c spectator hpair hnonzero⟩

theorem frame_val (a b c : ℕ) (spectator : State)
    (hpair : (a :: b :: c :: spectator).Pairwise MaskDisjoint)
    (hnonzero : ∀ x ∈ a :: b :: c :: spectator, x ≠ 0) :
    (frame a b c spectator hpair hnonzero).val = context a b c spectator := rfl

theorem outside_context (a b c : ℕ) (spectator : State) :
    outside (context a b c spectator) = spectator := by
  simp [outside, context]

/-- The only filter condition needed for an arbitrary transported mask. -/
theorem transport_mask (a b c : ℕ) (spectator : State) (m : ℕ)
    (hm : liftMask (context a b c spectator).label m ≠ 0) :
    transport (context a b c spectator) [m, 8, 16] =
      canonical ([liftMask (context a b c spectator).label m] ++ spectator) := by
  rw [transport_tripod, outside_context]
  simp only [List.filter_cons, decide_eq_true hm, ↓reduceIte, List.filter_nil]

theorem liftMask_7 (a b c : ℕ) (spectator : State) :
    liftMask (context a b c spectator).label 7 = a ||| b ||| c := by
  simp [liftMask, context, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem liftMask_3 (a b c : ℕ) (spectator : State) :
    liftMask (context a b c spectator).label 3 = a ||| b := by
  simp [liftMask, context, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem liftMask_5 (a b c : ℕ) (spectator : State) :
    liftMask (context a b c spectator).label 5 = a ||| c := by
  simp [liftMask, context, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem liftMask_6 (a b c : ℕ) (spectator : State) :
    liftMask (context a b c spectator).label 6 = b ||| c := by
  simp [liftMask, context, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem liftMask_4 (a b c : ℕ) (spectator : State) :
    liftMask (context a b c spectator).label 4 = c := by
  simp [liftMask, context, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem liftMask_2 (a b c : ℕ) (spectator : State) :
    liftMask (context a b c spectator).label 2 = b := by
  simp [liftMask, context, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem liftMask_1 (a b c : ℕ) (spectator : State) :
    liftMask (context a b c spectator).label 1 = a := by
  simp [liftMask, context, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem transport_7 (a b c : ℕ) (spectator : State)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    transport (context a b c spectator) [7, 8, 16] =
      canonical ((a ||| b ||| c) :: spectator) := by
  have hm : liftMask (context a b c spectator).label 7 ≠ 0 := by
    rw [liftMask_7]
    simp [ha, hb, hc]
  simpa only [liftMask_7, List.singleton_append] using transport_mask a b c spectator 7 hm

theorem transport_3 (a b c : ℕ) (spectator : State)
    (ha : a ≠ 0) (hb : b ≠ 0) (_hc : c ≠ 0) :
    transport (context a b c spectator) [3, 8, 16] = canonical ((a ||| b) :: spectator) := by
  have hm : liftMask (context a b c spectator).label 3 ≠ 0 := by
    rw [liftMask_3]
    simp [ha, hb]
  simpa only [liftMask_3, List.singleton_append] using transport_mask a b c spectator 3 hm

theorem transport_5 (a b c : ℕ) (spectator : State)
    (ha : a ≠ 0) (_hb : b ≠ 0) (hc : c ≠ 0) :
    transport (context a b c spectator) [5, 8, 16] = canonical ((a ||| c) :: spectator) := by
  have hm : liftMask (context a b c spectator).label 5 ≠ 0 := by
    rw [liftMask_5]
    simp [ha, hc]
  simpa only [liftMask_5, List.singleton_append] using transport_mask a b c spectator 5 hm

theorem transport_6 (a b c : ℕ) (spectator : State)
    (_ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    transport (context a b c spectator) [6, 8, 16] = canonical ((b ||| c) :: spectator) := by
  have hm : liftMask (context a b c spectator).label 6 ≠ 0 := by
    rw [liftMask_6]
    simp [hb, hc]
  simpa only [liftMask_6, List.singleton_append] using transport_mask a b c spectator 6 hm

theorem transport_4 (a b c : ℕ) (spectator : State)
    (_ha : a ≠ 0) (_hb : b ≠ 0) (hc : c ≠ 0) :
    transport (context a b c spectator) [4, 8, 16] = canonical (c :: spectator) := by
  have hm : liftMask (context a b c spectator).label 4 ≠ 0 := by rwa [liftMask_4]
  simpa only [liftMask_4, List.singleton_append] using transport_mask a b c spectator 4 hm

theorem transport_2 (a b c : ℕ) (spectator : State)
    (_ha : a ≠ 0) (hb : b ≠ 0) (_hc : c ≠ 0) :
    transport (context a b c spectator) [2, 8, 16] = canonical (b :: spectator) := by
  have hm : liftMask (context a b c spectator).label 2 ≠ 0 := by rwa [liftMask_2]
  simpa only [liftMask_2, List.singleton_append] using transport_mask a b c spectator 2 hm

theorem transport_1 (a b c : ℕ) (spectator : State)
    (ha : a ≠ 0) (_hb : b ≠ 0) (_hc : c ≠ 0) :
    transport (context a b c spectator) [1, 8, 16] = canonical (a :: spectator) := by
  have hm : liftMask (context a b c spectator).label 1 ≠ 0 := by rwa [liftMask_1]
  simpa only [liftMask_1, List.singleton_append] using transport_mask a b c spectator 1 hm

/-- An exact expansion for an arbitrary state functional. It asserts no vanishing. -/
theorem realization_localGamma (t : ℤ) (F : State → ℤ) (a b c : ℕ) (spectator : State)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    realization t (F ∘ transport (context a b c spectator)) (embed localGamma) =
      F (canonical ((a ||| b ||| c) :: spectator)) -
      F (canonical ((a ||| b) :: spectator)) -
      F (canonical ((a ||| c) :: spectator)) -
      F (canonical ((b ||| c) :: spectator)) +
      F (canonical (c :: spectator)) + F (canonical (b :: spectator)) +
      F (canonical (a :: spectator)) := by
  rw [realization_embed, localGamma_explicit]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Function.comp_apply, one_smul, neg_one_smul, add_zero,
    transport_7 a b c spectator ha hb hc, transport_3 a b c spectator ha hb hc,
    transport_5 a b c spectator ha hb hc, transport_6 a b c spectator ha hb hc,
    transport_4 a b c spectator ha hb hc, transport_2 a b c spectator ha hb hc,
    transport_1 a b c spectator ha hb hc]
  ring

/-- The same seven-state identity through the actual admissible-frame constructor. -/
theorem realization_frame (t : ℤ) (F : State → ℤ) (a b c : ℕ) (spectator : State)
    (hpair : (a :: b :: c :: spectator).Pairwise MaskDisjoint)
    (hnonzero : ∀ x ∈ a :: b :: c :: spectator, x ≠ 0) :
    realization t (F ∘ transport (frame a b c spectator hpair hnonzero).val) (embed localGamma) =
      F (canonical ((a ||| b ||| c) :: spectator)) -
      F (canonical ((a ||| b) :: spectator)) -
      F (canonical ((a ||| c) :: spectator)) -
      F (canonical ((b ||| c) :: spectator)) +
      F (canonical (c :: spectator)) + F (canonical (b :: spectator)) +
      F (canonical (a :: spectator)) :=
  realization_localGamma t F a b c spectator
    (hnonzero a (by simp)) (hnonzero b (by simp)) (hnonzero c (by simp))

end M9Native.CurvePowerThreeBlockContext

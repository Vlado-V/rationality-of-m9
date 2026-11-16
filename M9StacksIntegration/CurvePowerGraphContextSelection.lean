module

public import M9StacksIntegration.CurvePowerGraphDisjoint
public import M9StacksIntegration.CurvePowerGraphReframe

/-! Selection of the at most two outside blocks meeting chosen vertices.
The construction changes only the outside labels and their spectators. -/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphContextSelection

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphDisjoint
open CurvePowerGraphReframe CurvePowerGraphContextValidity

theorem pairwise_disjoint_of_mem {s : State} (hs : s.Pairwise MaskDisjoint)
    {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) : MaskDisjoint a b := by
  induction s with
  | nil => simp at ha
  | cons c s ih =>
      obtain ⟨hc, ht⟩ := List.pairwise_cons.mp hs
      rcases List.mem_cons.mp ha with hac | hat
      · subst a
        exact hc b ((List.mem_cons.mp hb).resolve_left hne.symm)
      · rcases List.mem_cons.mp hb with hbc | hbt
        · subst b
          exact maskDisjoint_symm (hc a hat)
        · exact ih ht hat hbt

theorem blockAt_mem_of_ne_zero (v : ℕ) (s : State) (hn : blockAt v s ≠ 0) :
    blockAt v s ∈ s := by
  induction s with
  | nil => simp [blockAt] at hn
  | cons a s ih =>
      by_cases ha : a.testBit v = true
      · simp [blockAt, ha]
      · have he : blockAt v (a :: s) = blockAt v s := by simp [blockAt, ha]
        rw [he] at hn ⊢
        exact List.mem_cons_of_mem a (ih hn)

theorem blockAt_testBit_of_ne_zero (v : ℕ) (s : State) (hn : blockAt v s ≠ 0) :
    (blockAt v s).testBit v = true := by
  induction s with
  | nil => simp [blockAt] at hn
  | cons a s ih =>
      by_cases ha : a.testBit v = true
      · simp [blockAt, ha]
      · have he : blockAt v (a :: s) = blockAt v s := by simp [blockAt, ha]
        rw [he] at hn ⊢
        exact ih hn

theorem blockAt_eq_zero_iff (v : ℕ) (s : State) :
    blockAt v s = 0 ↔ ∀ a ∈ s, a.testBit v = false := by
  induction s with
  | nil => simp [blockAt]
  | cons a s ih =>
      by_cases ha : a.testBit v = true
      · have hn : a ≠ 0 := by intro h; simp [h] at ha
        simp [blockAt, ha, hn]
      · have hf : a.testBit v = false := Bool.eq_false_iff.mpr ha
        simpa [blockAt, ha, hf] using ih

theorem outside_pairwise (ctx : Context) (hctx : DisjointContext ctx) :
    (outside ctx).Pairwise MaskDisjoint := by
  apply List.pairwise_append.mpr
  have hp : [ctx.label 3, ctx.label 4].Pairwise MaskDisjoint := by
    simpa [List.pairwise_cons] using hctx.labels 3 4 (by decide)
  refine ⟨hp.filter _, hctx.spectators, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp (List.mem_filter.mp ha).1 with rfl | ha
  · exact hctx.cross 3 b hb
  · have he : a = ctx.label 4 := by simpa using ha
    subst a
    exact hctx.cross 4 b hb

theorem outside_nonzero (ctx : Context) (hctx : DisjointContext ctx)
    (a : ℕ) (ha : a ∈ outside ctx) : a ≠ 0 := by
  rcases List.mem_append.mp ha with ha | ha
  · exact of_decide_eq_true (List.mem_filter.mp ha).2
  · exact hctx.spectator_nonzero a ha

theorem special_disjoint_outside (ctx : Context) (hctx : DisjointContext ctx)
    (i : Fin 5) (hi : i.val < 3) (a : ℕ) (ha : a ∈ outside ctx) :
    MaskDisjoint (ctx.label i) a := by
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_cons.mp (List.mem_filter.mp ha).1 with rfl | ha
    · exact hctx.labels i 3 (by intro h; subst i; norm_num at hi)
    · have he : a = ctx.label 4 := by simpa using ha
      subst a
      exact hctx.labels i 4 (by intro h; subst i; norm_num at hi)
  · exact hctx.cross i a ha

def reframe (ctx : Context) (a b : ℕ) (spectator : State) : Context where
  label := ![ctx.label 0, ctx.label 1, ctx.label 2, a, b]
  spectator := spectator

theorem outside_reframe (ctx : Context) (a b : ℕ) (spectator : State) :
    outside (reframe ctx a b spectator) = [a, b].filter (· ≠ 0) ++ spectator := rfl

theorem admissible_reframe (ctx : Context) (hctx : Admissible ctx)
    (a b : ℕ) (spectator : State)
    (ho : (outside ctx).Perm ([a, b].filter (· ≠ 0) ++ spectator)) :
    Admissible (reframe ctx a b spectator) := by
  have hp := (outside_pairwise ctx hctx.2).perm ho (fun h => maskDisjoint_symm h)
  obtain ⟨hpab, hps, hpc⟩ := List.pairwise_append.mp hp
  have hnonzero (x : ℕ) (hx : x ∈ [a, b].filter (· ≠ 0) ++ spectator) : x ≠ 0 :=
    outside_nonzero ctx hctx.2 x (ho.symm.subset hx)
  have hspecial (i : Fin 5) (hi : i.val < 3) (x : ℕ)
      (hx : x ∈ [a, b].filter (· ≠ 0) ++ spectator) : MaskDisjoint (ctx.label i) x :=
    special_disjoint_outside ctx hctx.2 i hi x (ho.symm.subset hx)
  have hs_a (i : Fin 5) (hi : i.val < 3) : MaskDisjoint (ctx.label i) a := by
    by_cases ha : a = 0
    · simp [ha, MaskDisjoint]
    · exact hspecial i hi a (by simp [ha])
  have hs_b (i : Fin 5) (hi : i.val < 3) : MaskDisjoint (ctx.label i) b := by
    by_cases hb : b = 0
    · simp [hb, MaskDisjoint]
    · exact hspecial i hi b (by simp [hb])
  have hab : MaskDisjoint a b := by
    by_cases ha : a = 0
    · simp [ha, MaskDisjoint]
    · by_cases hb : b = 0
      · simp [hb, MaskDisjoint]
      · simpa [ha, hb] using hpab
  have has (x : ℕ) (hx : x ∈ spectator) : MaskDisjoint a x := by
    by_cases ha : a = 0
    · simp [ha, MaskDisjoint]
    · exact hpc a (by simp [ha]) x hx
  have hbs (x : ℕ) (hx : x ∈ spectator) : MaskDisjoint b x := by
    by_cases hb : b = 0
    · simp [hb, MaskDisjoint]
    · exact hpc b (by simp [hb]) x hx
  refine ⟨?_, ?_, hps, ?_, ?_⟩
  · simpa [Valid, reframe] using hctx.1
  · intro i j hij
    have h01 := hctx.2.labels 0 1 (by decide)
    have h02 := hctx.2.labels 0 2 (by decide)
    have h12 := hctx.2.labels 1 2 (by decide)
    have h0a := hs_a 0 (by decide)
    have h1a := hs_a 1 (by decide)
    have h2a := hs_a 2 (by decide)
    have h0b := hs_b 0 (by decide)
    have h1b := hs_b 1 (by decide)
    have h2b := hs_b 2 (by decide)
    fin_cases i <;> fin_cases j <;> simp [reframe] at hij ⊢
    all_goals first | assumption | exact maskDisjoint_symm (by assumption)
  · intro i x hx
    fin_cases i
    · exact hspecial 0 (by decide) x (List.mem_append_right _ hx)
    · exact hspecial 1 (by decide) x (List.mem_append_right _ hx)
    · exact hspecial 2 (by decide) x (List.mem_append_right _ hx)
    · exact has x hx
    · exact hbs x hx
  · intro x hx
    exact hnonzero x (List.mem_append_right _ hx)

theorem blockAt_extract_perm (v : ℕ) (s : State) (hn : ∀ a ∈ s, a ≠ 0) :
    s.Perm ([blockAt v s].filter (· ≠ 0) ++ s.erase (blockAt v s)) := by
  by_cases hz : blockAt v s = 0
  · have h0 : 0 ∉ s := by intro h; exact hn 0 h rfl
    simp [hz, List.erase_of_not_mem h0]
  · simpa [hz] using List.perm_cons_erase (blockAt_mem_of_ne_zero v s hz)

theorem erase_blockAt_misses (v : ℕ) (s : State) (hp : s.Pairwise MaskDisjoint)
    (hn : s.Nodup) (a : ℕ) (ha : a ∈ s.erase (blockAt v s)) : a.testBit v = false := by
  by_cases hz : blockAt v s = 0
  · exact (blockAt_eq_zero_iff v s).mp hz a (List.mem_of_mem_erase ha)
  · apply Bool.eq_false_iff.mpr
    intro hv
    have hne := (hn.mem_erase_iff.mp ha).1
    exact (maskDisjoint_iff _ _).mp
      (pairwise_disjoint_of_mem hp (List.mem_of_mem_erase ha)
        (blockAt_mem_of_ne_zero v s hz) hne) v hv (blockAt_testBit_of_ne_zero v s hz)

def selectPair (ctx : Context) (v w : ℕ) : Context :=
  let s := outside ctx
  let a := blockAt v s
  let r := s.erase a
  let b := blockAt w r
  reframe ctx a b (r.erase b)

theorem selectPair_special (ctx : Context) (v w : ℕ) (i : Fin 5) (hi : i.val < 3) :
    (selectPair ctx v w).label i = ctx.label i := by
  fin_cases i <;> simp at hi
  all_goals rfl

theorem selectPair_outside_perm (ctx : Context) (hctx : Admissible ctx) (v w : ℕ) :
    (outside ctx).Perm (outside (selectPair ctx v w)) := by
  let s := outside ctx
  let a := blockAt v s
  let r := s.erase a
  let b := blockAt w r
  have hn : ∀ x ∈ s, x ≠ 0 := outside_nonzero ctx hctx.2
  have hrn : ∀ x ∈ r, x ≠ 0 := fun x hx => hn x (List.mem_of_mem_erase hx)
  have h1 := blockAt_extract_perm v s hn
  have h2 := (blockAt_extract_perm w r hrn).append_left ([a].filter (· ≠ 0))
  change s.Perm ([a, b].filter (· ≠ 0) ++ r.erase b)
  rw [show [a, b] = [a] ++ [b] from rfl, List.filter_append, List.append_assoc]
  exact h1.trans h2

theorem selectPair_admissible (ctx : Context) (hctx : Admissible ctx) (v w : ℕ) :
    Admissible (selectPair ctx v w) :=
  admissible_reframe ctx hctx _ _ _ (selectPair_outside_perm ctx hctx v w)

theorem selectPair_spectators_miss (ctx : Context) (hctx : Admissible ctx) (v w : ℕ)
    (a : ℕ) (ha : a ∈ (selectPair ctx v w).spectator) :
    a.testBit v = false ∧ a.testBit w = false := by
  have hp := outside_pairwise ctx hctx.2
  have hn := nodup_of_pairwise_nonzero _ hp (outside_nonzero ctx hctx.2)
  constructor
  · exact erase_blockAt_misses v _ hp hn a (List.mem_of_mem_erase ha)
  · exact erase_blockAt_misses w _ (hp.erase _) (hn.erase _) a ha

/-- Each chosen vertex is in a label, or is fixed in every transported state. -/
theorem selectPair_covered_or_marked (ctx : Context) (hctx : Admissible ctx) (v w : ℕ)
    (x : ℕ) (hx : x = v ∨ x = w) :
    (∃ i : Fin 5, ((selectPair ctx v w).label i).testBit x = true) ∨
      ((∀ i : Fin 5, ((selectPair ctx v w).label i).testBit x = false) ∧
        ∀ a ∈ (selectPair ctx v w).spectator, a.testBit x = false) := by
  by_cases h : ∃ i : Fin 5, ((selectPair ctx v w).label i).testBit x = true
  · exact Or.inl h
  · right
    refine ⟨fun i => Bool.eq_false_iff.mpr (fun hi => h ⟨i, hi⟩), ?_⟩
    intro a ha
    rcases hx with hx | hx
    · rw [hx]
      exact (selectPair_spectators_miss ctx hctx v w a ha).1
    · rw [hx]
      exact (selectPair_spectators_miss ctx hctx v w a ha).2

theorem selectPair_transport_localGamma (ctx : Context) (hctx : Admissible ctx)
    (v w : ℕ) (s : State) (hs : s ∈ keys (embed localGamma)) :
    transport ctx s = transport (selectPair ctx v w) s :=
  transport_localGamma_of_outside_perm ctx _
    (selectPair_special ctx v w 0 (by decide)).symm
    (selectPair_special ctx v w 1 (by decide)).symm
    (selectPair_special ctx v w 2 (by decide)).symm
    (selectPair_outside_perm ctx hctx v w) s hs

/-- A live label identifies exactly the corresponding local bit. -/
theorem liftMask_testBit_eq (ctx : Context) (hctx : DisjointContext ctx)
    (i : Fin 5) (v : ℕ) (hi : (ctx.label i).testBit v = true) (b : ℕ) :
    (liftMask ctx.label b).testBit v = b.testBit i.val := by
  apply Bool.eq_iff_iff.mpr
  rw [liftMask_testBit_iff]
  constructor
  · rintro ⟨j, hj, hjv⟩
    by_cases hji : j = i
    · simpa [hji] using hj
    · exact False.elim ((maskDisjoint_iff _ _).mp (hctx.labels j i hji) v hjv hi)
  · intro hb
    exact ⟨i, hb, hi⟩

end M9Native.CurvePowerGraphContextSelection

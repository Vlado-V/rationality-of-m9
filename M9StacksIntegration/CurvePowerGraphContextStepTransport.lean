module

public import M9StacksIntegration.CurvePowerGraphContextSelection

/-! Literal point and diagonal steps commute with disjoint block transport.
The result applies to every pairwise-disjoint source state, and hence to all
seven source states of the modified small diagonal. -/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphContextStepTransport

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphDisjoint
open CurvePowerGraphContextSelection

theorem liftMask_zero (f : Fin 5 → ℕ) : liftMask f 0 = 0 := by simp [liftMask]

theorem liftMask_or (f : Fin 5 → ℕ) (a b : ℕ) :
    liftMask f (a ||| b) = liftMask f a ||| liftMask f b := by
  apply Nat.eq_of_testBit_eq
  intro v
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.testBit_lor, Bool.or_eq_true, liftMask_testBit_iff]
  constructor
  · rintro ⟨i, hi, hiv⟩
    rcases hi with hi | hi
    · exact Or.inl ⟨i, hi, hiv⟩
    · exact Or.inr ⟨i, hi, hiv⟩
  · rintro (⟨i, hi, hiv⟩ | ⟨i, hi, hiv⟩)
    · exact ⟨i, Or.inl hi, hiv⟩
    · exact ⟨i, Or.inr hi, hiv⟩

theorem spectator_testBit_false (ctx : Context) (hctx : DisjointContext ctx)
    (i : Fin 5) (v : ℕ) (hi : (ctx.label i).testBit v = true)
    (a : ℕ) (ha : a ∈ ctx.spectator) : a.testBit v = false := by
  apply Bool.eq_false_iff.mpr
  exact fun hv => (maskDisjoint_iff _ _).mp (hctx.cross i a ha) v hi hv

theorem mem_transport_lift (ctx : Context) (s : State) (a : ℕ) (ha : a ∈ s)
    (hn : liftMask ctx.label a ≠ 0) : liftMask ctx.label a ∈ transport ctx s := by
  apply (canonical_perm _).symm.subset
  apply List.mem_append_left
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨a, ha, rfl⟩, by simpa using hn⟩

theorem blockAt_eq_of_pairwise (v : ℕ) (s : State) (hs : s.Pairwise MaskDisjoint)
    (a : ℕ) (ha : a ∈ s) (hv : a.testBit v = true) : blockAt v s = a := by
  have hn : blockAt v s ≠ 0 := by
    intro hz
    have hf := (blockAt_eq_zero_iff v s).mp hz a ha
    rw [hv] at hf
    contradiction
  by_contra hne
  exact (maskDisjoint_iff _ _).mp
    (pairwise_disjoint_of_mem hs (blockAt_mem_of_ne_zero v s hn) ha hne) v
    (blockAt_testBit_of_ne_zero v s hn) hv

theorem lift_blockAt_ne_zero (ctx : Context) (hctx : DisjointContext ctx)
    (i : Fin 5) (v : ℕ) (hi : (ctx.label i).testBit v = true)
    (s : State) (hn : blockAt i.val s ≠ 0) :
    liftMask ctx.label (blockAt i.val s) ≠ 0 := by
  have hv := liftMask_testBit_eq ctx hctx i v hi (blockAt i.val s)
  rw [blockAt_testBit_of_ne_zero i.val s hn] at hv
  intro hz
  simp [hz] at hv

theorem blockAt_transport (ctx : Context) (hctx : DisjointContext ctx)
    (i : Fin 5) (v : ℕ) (hi : (ctx.label i).testBit v = true)
    (s : State) (hs : s.Pairwise MaskDisjoint) :
    blockAt v (transport ctx s) = liftMask ctx.label (blockAt i.val s) := by
  by_cases hz : blockAt i.val s = 0
  · rw [hz, liftMask_zero]
    apply (blockAt_eq_zero_iff v _).mpr
    intro a ha
    have hm := (canonical_perm _).subset ha
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hm).1
      rw [liftMask_testBit_eq ctx hctx i v hi b]
      exact (blockAt_eq_zero_iff i.val s).mp hz b hb
    · exact spectator_testBit_false ctx hctx i v hi a hm
  · apply blockAt_eq_of_pairwise v _ (transport_pairwise ctx hctx s hs)
    · exact mem_transport_lift ctx s _ (blockAt_mem_of_ne_zero i.val s hz)
        (lift_blockAt_ne_zero ctx hctx i v hi s hz)
    · rw [liftMask_testBit_eq ctx hctx i v hi]
      exact blockAt_testBit_of_ne_zero i.val s hz

theorem canonical_erase (s : State) (a : ℕ) :
    (canonical s).erase a = canonical (s.erase a) := by
  have hp : (canonical s).Pairwise (· ≤ ·) := by
    rw [canonical_eq_insertionSort]
    exact List.pairwise_insertionSort _ _
  calc
    (canonical s).erase a = canonical ((canonical s).erase a) := by
      exact ((canonical_eq_insertionSort _).trans (hp.erase a).insertionSort_eq).symm
    _ = canonical (s.erase a) := canonical_eq_of_perm ((canonical_perm s).erase a)

theorem map_erase_of_unique (f : ℕ → ℕ) (s : State) (a : ℕ)
    (h : ∀ b ∈ s, f b = f a → b = a) :
    (s.erase a).map f = (s.map f).erase (f a) := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      by_cases hb : b = a
      · subst b
        simp
      · have hfb : f b ≠ f a := fun he => hb (h b List.mem_cons_self he)
        have ht : ∀ b ∈ s, f b = f a → b = a :=
          fun b hb he => h b (List.mem_cons_of_mem _ hb) he
        simpa [hb, hfb] using congrArg (fun l => f b :: l) (ih ht)

theorem lift_unique_at (ctx : Context) (hctx : DisjointContext ctx)
    (s : State) (hs : s.Pairwise MaskDisjoint) (a : ℕ) (ha : a ∈ s)
    (hn : liftMask ctx.label a ≠ 0) (b : ℕ) (hb : b ∈ s)
    (he : liftMask ctx.label b = liftMask ctx.label a) : b = a := by
  by_contra hne
  have hd := liftMask_disjoint ctx.label hctx.labels b a
    (pairwise_disjoint_of_mem hs hb ha hne)
  rw [he] at hd
  exact hn (by simpa only [MaskDisjoint, Nat.and_self] using hd)

theorem transport_erase (ctx : Context) (hctx : DisjointContext ctx)
    (s : State) (hs : s.Pairwise MaskDisjoint) (a : ℕ) (ha : a ∈ s)
    (hn : liftMask ctx.label a ≠ 0) :
    (transport ctx s).erase (liftMask ctx.label a) = transport ctx (s.erase a) := by
  have hm : liftMask ctx.label a ∈ (s.map (liftMask ctx.label)).filter (· ≠ 0) :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨a, ha, rfl⟩, by simpa using hn⟩
  have he := map_erase_of_unique (liftMask ctx.label) s a
    (lift_unique_at ctx hctx s hs a ha hn)
  simp only [transport]
  rw [canonical_erase, List.erase_append_left _ hm, List.erase_filter, ← he]

theorem transport_join (ctx : Context) (a b : ℕ) (s : State)
    (hn : liftMask ctx.label a ||| liftMask ctx.label b ≠ 0) :
    transport ctx (canonical ((a ||| b) :: s)) =
      canonical ((liftMask ctx.label a ||| liftMask ctx.label b) :: transport ctx s) := by
  rw [transport_canonical]
  change canonical ((((liftMask ctx.label (a ||| b)) :: s.map (liftMask ctx.label)).filter
      (· ≠ 0)) ++ ctx.spectator) = _
  rw [liftMask_or]
  simp only [List.filter_cons, decide_eq_true_eq, ite_eq_left hn, List.cons_append]
  apply canonical_eq_of_perm
  exact ((canonical_perm _).cons _).symm

theorem pointStep_transport_pairwise (ctx : Context) (hctx : DisjointContext ctx)
    (i : Fin 5) (v : ℕ) (hi : (ctx.label i).testBit v = true)
    (s : State) (hs : s.Pairwise MaskDisjoint) :
    pointStep v (transport ctx s) = (pointStep i.val s).map (transport ctx) := by
  have hB := blockAt_transport ctx hctx i v hi s hs
  by_cases hz : blockAt i.val s = 0
  · simp [pointStep, hB, hz, liftMask_zero]
  · have hf := lift_blockAt_ne_zero ctx hctx i v hi s hz
    simp only [pointStep, hB, ite_eq_right hz, ite_eq_right hf, Option.map_some]
    exact congrArg some (transport_erase ctx hctx s hs _
      (blockAt_mem_of_ne_zero i.val s hz) hf)

theorem diagonalStep_transport_pairwise (ctx : Context) (hctx : DisjointContext ctx)
    (i j : Fin 5) (v w : ℕ) (hi : (ctx.label i).testBit v = true)
    (hj : (ctx.label j).testBit w = true) (s : State) (hs : s.Pairwise MaskDisjoint) :
    diagonalStep v w (transport ctx s) =
      (diagonalStep i.val j.val s).map (fun p => (transport ctx p.1, p.2)) := by
  have hA := blockAt_transport ctx hctx i v hi s hs
  have hB := blockAt_transport ctx hctx j w hj s hs
  by_cases ha : blockAt i.val s = 0
  · by_cases hb : blockAt j.val s = 0
    · simp [diagonalStep, hA, hB, ha, hb, liftMask_zero]
    · have hfb := lift_blockAt_ne_zero ctx hctx j w hj s hb
      simp only [diagonalStep, hA, hB, ha, liftMask_zero, ite_eq_right hb, ite_eq_right hfb]
      exact congrArg (fun l => some (l, false)) (transport_erase ctx hctx s hs _
        (blockAt_mem_of_ne_zero j.val s hb) hfb)
  · have hfa := lift_blockAt_ne_zero ctx hctx i v hi s ha
    by_cases hb : blockAt j.val s = 0
    · simp only [diagonalStep, hA, hB, hb, liftMask_zero, ite_eq_right ha, ite_eq_right hfa]
      exact congrArg (fun l => some (l, false)) (transport_erase ctx hctx s hs _
        (blockAt_mem_of_ne_zero i.val s ha) hfa)
    · have hfb := lift_blockAt_ne_zero ctx hctx j w hj s hb
      have hma := blockAt_mem_of_ne_zero i.val s ha
      have hmb := blockAt_mem_of_ne_zero j.val s hb
      by_cases hab : blockAt i.val s = blockAt j.val s
      · simp only [diagonalStep, hA, hB, ite_eq_right hb, ite_eq_right hfb, hab]
        exact congrArg (fun l => some (l, true)) (transport_erase ctx hctx s hs _ hmb hfb)
      · have hfab : liftMask ctx.label (blockAt i.val s) ≠
            liftMask ctx.label (blockAt j.val s) := by
          intro he
          exact hab (lift_unique_at ctx hctx s hs _ hmb hfb _ hma he)
        have hmb' : blockAt j.val s ∈ s.erase (blockAt i.val s) :=
          (List.mem_erase_of_ne (Ne.symm hab)).mpr hmb
        have he1 := transport_erase ctx hctx s hs _ hma hfa
        have he2 := transport_erase ctx hctx (s.erase (blockAt i.val s)) (hs.erase _)
          _ hmb' hfb
        have hUnion : liftMask ctx.label (blockAt i.val s) |||
            liftMask ctx.label (blockAt j.val s) ≠ 0 :=
          fun h => hfa (Nat.or_eq_zero_iff.mp h).1
        simp only [diagonalStep, hA, hB, ite_eq_right ha, ite_eq_right hb, ite_eq_right hfa,
          ite_eq_right hfb, ite_eq_right hab, ite_eq_right hfab, Option.map_some]
        rw [he1, he2, transport_join ctx _ _ _ hUnion]

theorem pointStep_transport (ctx : Context) (hctx : Admissible ctx)
    (i : Fin 5) (v : ℕ) (hi : (ctx.label i).testBit v = true)
    (s : State) (hs : s ∈ keys (embed localGamma)) :
    pointStep v (transport ctx s) = (pointStep i.val s).map (transport ctx) :=
  pointStep_transport_pairwise ctx hctx.2 i v hi s (localGamma_pairwise s hs)

theorem diagonalStep_transport (ctx : Context) (hctx : Admissible ctx)
    (i j : Fin 5) (v w : ℕ) (hi : (ctx.label i).testBit v = true)
    (hj : (ctx.label j).testBit w = true) (s : State)
    (hs : s ∈ keys (embed localGamma)) :
    diagonalStep v w (transport ctx s) =
      (diagonalStep i.val j.val s).map (fun p => (transport ctx p.1, p.2)) :=
  diagonalStep_transport_pairwise ctx hctx.2 i j v w hi hj s (localGamma_pairwise s hs)

end M9Native.CurvePowerGraphContextStepTransport

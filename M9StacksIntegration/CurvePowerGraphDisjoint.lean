module

public import M9StacksIntegration.CurvePowerGraphContextValidity
public import M9StacksIntegration.CurvePowerGraphMapReindex

/-!
# Disjoint block contexts and their actual partition-map hypotheses

The conditions below concern only bit sets of vertices. They imply the
separation and absence of duplicate blocks required by the checked
actual product-map comparisons. No intersection or numerical identity
is part of these conditions.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphDisjoint

open CurvePowerGraphLocal CurvePowerGraphContexts CurvePowerGraphMapReindex

def MaskDisjoint (a b : ℕ) : Prop := a &&& b = 0

instance maskDisjointDecidable : DecidableRel MaskDisjoint :=
  fun a b => inferInstanceAs (Decidable (a &&& b = 0))

theorem maskDisjoint_iff (a b : ℕ) : MaskDisjoint a b ↔
    ∀ v, a.testBit v = true → b.testBit v = true → False := by
  constructor
  · intro h v ha hb
    have ht := congrArg (fun x : ℕ => x.testBit v) h
    simp [ha, hb] at ht
  · intro h
    apply Nat.eq_of_testBit_eq
    intro v
    cases ha : a.testBit v <;> cases hb : b.testBit v <;>
      simp_all

theorem maskDisjoint_symm {a b : ℕ} (h : MaskDisjoint a b) : MaskDisjoint b a := by
  simpa only [MaskDisjoint, Nat.land_comm] using h

theorem liftMask_testBit_iff (f : Fin 5 → ℕ) (b v : ℕ) :
    (liftMask f b).testBit v = true ↔
      ∃ i : Fin 5, b.testBit i.val = true ∧ (f i).testBit v = true := by
  have hh (q : Bool) (a : ℕ) :
      (if q then a else 0).testBit v = true ↔ q = true ∧ a.testBit v = true := by
    cases q <;> simp
  simp only [liftMask, Nat.testBit_lor, Bool.or_eq_true, hh]
  simp [Fin.exists_fin_succ, or_assoc]

theorem liftMask_disjoint (f : Fin 5 → ℕ)
    (hf : ∀ i j : Fin 5, i ≠ j → MaskDisjoint (f i) (f j))
    (a b : ℕ) (hab : MaskDisjoint a b) : MaskDisjoint (liftMask f a) (liftMask f b) := by
  apply (maskDisjoint_iff _ _).mpr
  intro v ha hb
  obtain ⟨i, hi, hfi⟩ := (liftMask_testBit_iff f a v).mp ha
  obtain ⟨j, hj, hfj⟩ := (liftMask_testBit_iff f b v).mp hb
  by_cases hij : i = j
  · subst j
    exact (maskDisjoint_iff a b).mp hab i.val hi hj
  · exact (maskDisjoint_iff _ _).mp (hf i j hij) v hfi hfj

structure DisjointContext (ctx : Context) : Prop where
  labels : ∀ i j : Fin 5, i ≠ j → MaskDisjoint (ctx.label i) (ctx.label j)
  spectators : ctx.spectator.Pairwise MaskDisjoint
  cross : ∀ i : Fin 5, ∀ a ∈ ctx.spectator, MaskDisjoint (ctx.label i) a
  spectator_nonzero : ∀ a ∈ ctx.spectator, a ≠ 0

theorem liftMask_disjoint_spectator (ctx : Context) (hctx : DisjointContext ctx)
    (b a : ℕ) (ha : a ∈ ctx.spectator) : MaskDisjoint (liftMask ctx.label b) a := by
  apply (maskDisjoint_iff _ _).mpr
  intro v hb hav
  obtain ⟨i, _, hiv⟩ := (liftMask_testBit_iff ctx.label b v).mp hb
  exact (maskDisjoint_iff _ _).mp (hctx.cross i a ha) v hiv hav

theorem transport_pairwise (ctx : Context) (hctx : DisjointContext ctx)
    (s : State) (hs : s.Pairwise MaskDisjoint) : (transport ctx s).Pairwise MaskDisjoint := by
  have hm : (s.map (liftMask ctx.label)).Pairwise MaskDisjoint :=
    hs.map _ (fun a b hab => liftMask_disjoint ctx.label hctx.labels a b hab)
  have hf := hm.filter (· ≠ 0)
  have ha : (((s.map (liftMask ctx.label)).filter (· ≠ 0)) ++ ctx.spectator).Pairwise
      MaskDisjoint := by
    apply List.pairwise_append.mpr
    refine ⟨hf, hctx.spectators, ?_⟩
    intro a ha b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp ha).1
    exact liftMask_disjoint_spectator ctx hctx x b hb
  exact ha.perm (canonical_perm _).symm (fun h => maskDisjoint_symm h)

theorem transport_nonzero (ctx : Context) (hctx : DisjointContext ctx) (s : State)
    (a : ℕ) (ha : a ∈ transport ctx s) : a ≠ 0 := by
  have hm := (canonical_perm _).subset ha
  rcases List.mem_append.mp hm with h | h
  · exact of_decide_eq_true (List.mem_filter.mp h).2
  · exact hctx.spectator_nonzero a h

theorem nodup_of_pairwise_nonzero (s : State) (hs : s.Pairwise MaskDisjoint)
    (hn : ∀ a ∈ s, a ≠ 0) : s.Nodup := by
  apply List.Pairwise.imp_of_mem (p := hs)
  intro a b ha hb hab he
  subst b
  apply hn a ha
  simpa only [MaskDisjoint, Nat.and_self] using hab

theorem separated_of_pairwise (s : State) (hs : s.Pairwise MaskDisjoint) : Separated s := by
  intro v i j hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (maskDisjoint_iff _ _).mp (hs.rel_get_of_lt hij) v hi hj
  · exact (maskDisjoint_iff _ _).mp (hs.rel_get_of_lt hji) v hj hi

theorem transport_nodup (ctx : Context) (hctx : DisjointContext ctx)
    (s : State) (hs : s.Pairwise MaskDisjoint) : (transport ctx s).Nodup :=
  nodup_of_pairwise_nonzero _ (transport_pairwise ctx hctx s hs)
    (transport_nonzero ctx hctx s)

theorem transport_separated (ctx : Context) (hctx : DisjointContext ctx)
    (s : State) (hs : s.Pairwise MaskDisjoint) : Separated (transport ctx s) :=
  separated_of_pairwise _ (transport_pairwise ctx hctx s hs)

theorem localGamma_pairwise (s : State) (hs : s ∈ keys (embed localGamma)) :
    s.Pairwise MaskDisjoint := by
  have hc : (keys (embed localGamma)).all (fun s => decide (s.Pairwise MaskDisjoint)) = true := by
    decide
  exact of_decide_eq_true ((List.all_eq_true.mp hc) s hs)

theorem pointAction_pairwise (i : Fin 5) (s : State)
    (hs : s ∈ keys (pointAction i.val localGamma)) : s.Pairwise MaskDisjoint := by
  have hc : ∀ i : Fin 5, (keys (pointAction i.val localGamma)).all
      (fun s => decide (s.Pairwise MaskDisjoint)) = true := by
    decide
  exact of_decide_eq_true ((List.all_eq_true.mp (hc i)) s hs)

theorem diagonalAction_pairwise (i j : Fin 5) (s : State)
    (hs : s ∈ keys (diagonalAction i.val j.val localGamma)) : s.Pairwise MaskDisjoint := by
  have hc : ∀ i j : Fin 5, (keys (diagonalAction i.val j.val localGamma)).all
      (fun s => decide (s.Pairwise MaskDisjoint)) = true := by
    decide
  exact of_decide_eq_true ((List.all_eq_true.mp (hc i j)) s hs)

theorem transported_localGamma_actual_map_properties (ctx : Context)
    (hctx : DisjointContext ctx) (s : State) (hs : s ∈ keys (embed localGamma)) :
    (transport ctx s).Nodup ∧ Separated (transport ctx s) :=
  ⟨transport_nodup ctx hctx s (localGamma_pairwise s hs),
    transport_separated ctx hctx s (localGamma_pairwise s hs)⟩

theorem maskDisjoint_or_left {a b c : ℕ} (ha : MaskDisjoint a c) (hb : MaskDisjoint b c) :
    MaskDisjoint (a ||| b) c := by
  apply (maskDisjoint_iff _ _).mpr
  intro v hv hc
  rw [Nat.testBit_lor] at hv
  have hv' : a.testBit v = true ∨ b.testBit v = true := by
    simpa only [Bool.or_eq_true] using hv
  rcases hv' with h | h
  · exact (maskDisjoint_iff _ _).mp ha v h hc
  · exact (maskDisjoint_iff _ _).mp hb v h hc

theorem maskDisjoint_or_right {a b c : ℕ} (ha : MaskDisjoint a b) (hc : MaskDisjoint a c) :
    MaskDisjoint a (b ||| c) :=
  maskDisjoint_symm (maskDisjoint_or_left (maskDisjoint_symm ha) (maskDisjoint_symm hc))

theorem disjoint_pin (ctx : Context) (hctx : DisjointContext ctx) (i : Fin 5) :
    DisjointContext (pin ctx i) := by
  constructor
  · intro a b hab
    by_cases hai : a = i
    · subst a
      simp [pin, MaskDisjoint]
    · by_cases hbi : b = i
      · subst b
        simp [pin, MaskDisjoint]
      · simpa [pin, hai, hbi] using hctx.labels a b hab
  · exact hctx.spectators
  · intro a b hb
    by_cases hai : a = i
    · subst a
      simp [pin, MaskDisjoint]
    · simpa [pin, hai] using hctx.cross a b hb
  · exact hctx.spectator_nonzero

theorem disjoint_merge (ctx : Context) (hctx : DisjointContext ctx) (i j : Fin 5) :
    DisjointContext (merge ctx i j) := by
  constructor
  · intro a b hab
    by_cases haj : a = j
    · subst a
      simp [merge, MaskDisjoint]
    · by_cases hbj : b = j
      · subst b
        simp [merge, MaskDisjoint]
      · by_cases hai : a = i
        · subst a
          have hbi : b ≠ i := Ne.symm hab
          have hx := maskDisjoint_or_left (hctx.labels i b hab)
            (hctx.labels j b (Ne.symm hbj))
          simpa [merge, haj, hbj, hbi] using hx
        · by_cases hbi : b = i
          · subst b
            have hx := maskDisjoint_or_right (hctx.labels a i hab) (hctx.labels a j haj)
            simpa [merge, haj, hbj, hai] using hx
          · simpa [merge, haj, hbj, hai, hbi] using hctx.labels a b hab
  · exact hctx.spectators
  · intro a b hb
    by_cases haj : a = j
    · subst a
      simp [merge, MaskDisjoint]
    · by_cases hai : a = i
      · subst a
        have hx := maskDisjoint_or_left (hctx.cross i b hb) (hctx.cross j b hb)
        simpa [merge, haj] using hx
      · simpa [merge, haj, hai] using hctx.cross a b hb
  · exact hctx.spectator_nonzero

theorem rebase_child_pin_or_merge (t : ℤ) (ctx : Context)
    (kind : CurvePowerGraphInduction.LocalKind) (w : ℤ) (child : Context)
    (h : rebase t ctx kind = some (w, child)) :
    (∃ i, child = pin ctx i) ∨ ∃ i j, child = merge ctx i j := by
  cases kind with
  | point i =>
      simp only [rebase] at h
      split_ifs at h
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inl ⟨i, h.2.symm⟩
  | diagonal i j =>
      simp only [rebase] at h
      split_ifs at h
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        first
        | exact Or.inl ⟨i, h.2.symm⟩
        | exact Or.inr ⟨i, j, h.2.symm⟩
        | exact Or.inr ⟨j, i, h.2.symm⟩

theorem disjoint_rebase (t : ℤ) (ctx : Context) (hctx : DisjointContext ctx)
    (kind : CurvePowerGraphInduction.LocalKind) (w : ℤ) (child : Context)
    (h : rebase t ctx kind = some (w, child)) : DisjointContext child := by
  rcases rebase_child_pin_or_merge t ctx kind w child h with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact disjoint_pin ctx hctx i
  · exact disjoint_merge ctx hctx i j

def Admissible (ctx : Context) : Prop :=
  CurvePowerGraphContextValidity.Valid ctx ∧ DisjointContext ctx

theorem admissible_rebase (t : ℤ) (ctx : Context) (hctx : Admissible ctx)
    (kind : CurvePowerGraphInduction.LocalKind) (w : ℤ) (child : Context)
    (h : rebase t ctx kind = some (w, child)) : Admissible child :=
  ⟨CurvePowerGraphContextValidity.valid_rebase t ctx hctx.1 kind w child h,
    disjoint_rebase t ctx hctx.2 kind w child h⟩

end M9Native.CurvePowerGraphDisjoint

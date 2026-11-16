module

public import M9StacksIntegration.CurvePowerDiagonalJoinCanonical

/-!
# Actual two-factor restrictions on three free partition blocks

Each identity contracts the original point or diagonal line class on the
actual coordinate graph. State permutations and literal bitwise unions
retain the original Chow-cap functional throughout.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerThreeBlockWords

open CurvePowerGraphLocal CurvePowerGraphDisjoint CurvePowerGraphMapReindex
open CurvePowerChowFunctional CurvePowerDiagonalJoinCanonical

/-- Disjointness separates two nonzero masks. -/
theorem mask_ne {a b : ℕ} (h : MaskDisjoint a b) (ha : a ≠ 0) : a ≠ b := by
  rintro rfl
  exact ha (by simpa only [MaskDisjoint, Nat.and_self] using h)

theorem erased_nonzero {s : State} (hn : ∀ x ∈ s, x ≠ 0) (a : ℕ) :
    ∀ x ∈ s.erase a, x ≠ 0 := fun x hx => hn x (List.mem_of_mem_erase hx)

theorem first_third_ne {a b c : ℕ} {s : State}
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0) : a ≠ c :=
  mask_ne ((List.pairwise_cons.mp hp).1 c (by simp)) (hn a (by simp))

theorem middle_third_ne {a b c : ℕ} {s : State}
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0) : b ≠ c :=
  mask_ne ((List.pairwise_cons.mp hp.tail).1 c (by simp)) (hn b (by simp))

theorem outer_join_pairwise {a b c : ℕ} {s : State}
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0) :
    ((a ||| c) :: b :: s).Pairwise MaskDisjoint := by
  have h := joined_pairwise hp a c (by simp) (by simp) (first_third_ne hp hn)
  simpa [middle_third_ne hp hn] using h

theorem outer_join_nonzero {a b c : ℕ} {s : State}
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0) :
    ∀ x ∈ (a ||| c) :: b :: s, x ≠ 0 := by
  have h := joined_nonzero hn a c (by simp)
  simpa [middle_third_ne hp hn] using h

/-- The seven actual one-block targets of a three-block two-factor word. -/
def targets (a b c : ℕ) (s : State) : List State :=
  [(a ||| b ||| c) :: s, (a ||| b) :: s, (a ||| c) :: s,
    (b ||| c) :: s, c :: s, b :: s, a :: s]

/-- Literal disjointness and nonzeroness are retained in all seven targets. -/
theorem target_properties {a b c : ℕ} {s : State}
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0) :
    ∀ t ∈ targets a b c s, t.Pairwise MaskDisjoint ∧ ∀ x ∈ t, x ≠ 0 := by
  have hA : ∀ x ∈ s, MaskDisjoint a x :=
    fun x hx => (List.pairwise_cons.mp hp).1 x (by simp [hx])
  have hB : ∀ x ∈ s, MaskDisjoint b x :=
    fun x hx => (List.pairwise_cons.mp hp.tail).1 x (by simp [hx])
  have hD : ∀ x ∈ s, MaskDisjoint c x :=
    fun x hx => (List.pairwise_cons.mp hp.tail.tail).1 x (by simp [hx])
  have ha : a ≠ 0 := hn a (by simp)
  have hb : b ≠ 0 := hn b (by simp)
  have hc : c ≠ 0 := hn c (by simp)
  have hns : ∀ x ∈ s, x ≠ 0 := fun x hx => hn x (by simp [hx])
  have mk (m : ℕ) (hm : ∀ x ∈ s, MaskDisjoint m x) (hmn : m ≠ 0) :
      (m :: s).Pairwise MaskDisjoint ∧ ∀ x ∈ m :: s, x ≠ 0 := by
    refine ⟨List.pairwise_cons.mpr ⟨hm, hp.tail.tail.tail⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hmn
    · exact hns x hx
  have hab : a ||| b ≠ 0 := fun h => ha (Nat.or_eq_zero_iff.mp h).1
  have hac : a ||| c ≠ 0 := fun h => ha (Nat.or_eq_zero_iff.mp h).1
  have hbc : b ||| c ≠ 0 := fun h => hb (Nat.or_eq_zero_iff.mp h).1
  have habc : a ||| b ||| c ≠ 0 := fun h => hab (Nat.or_eq_zero_iff.mp h).1
  intro t ht
  simp only [targets, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mk _ (fun x hx => maskDisjoint_or_left
      (maskDisjoint_or_left (hA x hx) (hB x hx)) (hD x hx)) habc
  · exact mk _ (fun x hx => maskDisjoint_or_left (hA x hx) (hB x hx)) hab
  · exact mk _ (fun x hx => maskDisjoint_or_left (hA x hx) (hD x hx)) hac
  · exact mk _ (fun x hx => maskDisjoint_or_left (hB x hx) (hD x hx)) hbc
  · exact mk _ hD hc
  · exact mk _ hB hb
  · exact mk _ hA ha

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

omit [IsAlgClosed k] [IsVariety k C.hom] in
/-- Genuine coordinate permutation invariance of the actual functional. -/
theorem state_perm (ambient : ℕ) (word : List (Letter ambient)) (s t : State)
    (hp : s.Pairwise MaskDisjoint) (hn : ∀ x ∈ s, x ≠ 0) (hst : s.Perm t) :
    tautologicalFunctional k C c₀ ambient word s =
      tautologicalFunctional k C c₀ ambient word t := by
  have hs := nodup_of_pairwise_nonzero s hp hn
  exact CurvePowerPairingReindex.partitionFunctional_state_perm k C c₀ ambient
    (word.map (letterClass k C c₀ ambient)) s t hs (hst.nodup_iff.mp hs)
      (separated_of_pairwise s hp) hst

include hC

/-- First join a to c, then join the remaining free block b. -/
theorem diagonal_diagonal (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,l) :: .inr (j,l) :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail ((a ||| b ||| c) :: s) := by
  have hbc := middle_third_ne hp hn
  have hac := first_third_ne hp hn
  have h₁ := CurvePowerDiagonalJoinRestriction.tautologicalFunctional_diagonal_free_blocks
    k C c₀ hC ambient i l (.inr (j,l) :: tail) (a :: b :: c :: s)
    (nodup_of_pairwise_nonzero _ hp hn) (separated_of_pairwise _ hp)
    a c (by simp) (by simp) hac hi hl
  have hp' := outer_join_pairwise hp hn
  have hn' := outer_join_nonzero hp hn
  have hmb : (a ||| c) ≠ b :=
    mask_ne ((List.pairwise_cons.mp hp').1 b (by simp)) (hn' _ (by simp))
  have hl' : (a ||| c).testBit l.val = true := by simp [hl]
  have h₂ := CurvePowerDiagonalJoinRestriction.tautologicalFunctional_diagonal_free_blocks
    k C c₀ hC ambient j l tail ((a ||| c) :: b :: s)
    (nodup_of_pairwise_nonzero _ hp' hn') (separated_of_pairwise _ hp')
    b (a ||| c) (by simp) (by simp) hmb.symm hj hl'
  have h₁' : tautologicalFunctional k C c₀ ambient (.inr (i,l) :: .inr (j,l) :: tail)
      (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient (.inr (j,l) :: tail) ((a ||| c) :: b :: s) := by
    simpa [hbc] using h₁
  have hu : b ||| (a ||| c) = a ||| b ||| c := by
    rw [CurvePowerGraphContexts.lor_left_comm, ← Nat.lor_assoc]
  exact h₁'.trans (by simpa [hmb, hmb.symm, hu] using h₂)

/-- Join a to c and restrict the independent point in b. -/
theorem diagonal_point_ac (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,l) :: .inl j :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail ((a ||| c) :: s) := by
  have hbc := middle_third_ne hp hn
  have h₁ := CurvePowerDiagonalJoinRestriction.tautologicalFunctional_diagonal_free_blocks
    k C c₀ hC ambient i l (.inl j :: tail) (a :: b :: c :: s)
    (nodup_of_pairwise_nonzero _ hp hn) (separated_of_pairwise _ hp)
    a c (by simp) (by simp) (first_third_ne hp hn) hi hl
  have hp' := outer_join_pairwise hp hn
  have hn' := outer_join_nonzero hp hn
  have hmb : (a ||| c) ≠ b :=
    mask_ne ((List.pairwise_cons.mp hp').1 b (by simp)) (hn' _ (by simp))
  have h₂ := CurvePowerPointRestriction.tautologicalFunctional_point_free_block
    k C c₀ hC ambient j tail ((a ||| c) :: b :: s)
    (nodup_of_pairwise_nonzero _ hp' hn') (separated_of_pairwise _ hp') b (by simp) hj
  have h₁' : tautologicalFunctional k C c₀ ambient (.inr (i,l) :: .inl j :: tail)
      (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient (.inl j :: tail) ((a ||| c) :: b :: s) := by
    simpa [hbc] using h₁
  exact h₁'.trans (by simpa [hmb, hmb.symm] using h₂)

/-- Join b to c and restrict the independent point in a. -/
theorem diagonal_point_bc (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (j,l) :: .inl i :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail ((b ||| c) :: s) := by
  have p : (a :: b :: c :: s).Perm (b :: a :: c :: s) := List.Perm.swap b a _
  exact (state_perm k C c₀ ambient _ _ _ hp hn p).trans
    (diagonal_point_ac k C c₀ hC ambient b a c s j i l tail
      (hp.perm p (fun h => maskDisjoint_symm h))
      (fun x hx => hn x (p.mem_iff.mpr hx)) hj hi hl)

/-- Join a to b and restrict the independent point in c. -/
theorem diagonal_point_ab (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: .inl l :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail ((a ||| b) :: s) := by
  have p : (a :: b :: c :: s).Perm (a :: c :: b :: s) := (List.Perm.swap c b s).cons a
  exact (state_perm k C c₀ ambient _ _ _ hp hn p).trans
    (diagonal_point_ac k C c₀ hC ambient a c b s i l j tail
      (hp.perm p (fun h => maskDisjoint_symm h))
      (fun x hx => hn x (p.mem_iff.mpr hx)) hi hl hj)

/-- Restrict the independent points in a and b. -/
theorem point_point_ab (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (_hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (_hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inl i :: .inl j :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (c :: s) := by
  exact (CurvePowerPointRestriction.tautologicalFunctional_point_head
    k C c₀ hC ambient a (b :: c :: s) i (.inl j :: tail) hi
      (separated_of_pairwise _ hp)).trans
    (CurvePowerPointRestriction.tautologicalFunctional_point_head
      k C c₀ hC ambient b (c :: s) j tail hj (separated_of_pairwise _ hp.tail))

/-- Restrict the independent points in a and c. -/
theorem point_point_ac (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inl i :: .inl l :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (b :: s) := by
  have p : (a :: b :: c :: s).Perm (a :: c :: b :: s) := (List.Perm.swap c b s).cons a
  exact (state_perm k C c₀ ambient _ _ _ hp hn p).trans
    (point_point_ab k C c₀ hC ambient a c b s i l j tail
      (hp.perm p (fun h => maskDisjoint_symm h))
      (fun x hx => hn x (p.mem_iff.mpr hx)) hi hl hj)

/-- Restrict the independent points in b and c. -/
theorem point_point_bc (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inl j :: .inl l :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (a :: s) := by
  have p : (a :: b :: c :: s).Perm (b :: c :: a :: s) :=
    (List.Perm.swap b a (c :: s)).trans ((List.Perm.swap c a s).cons b)
  exact (state_perm k C c₀ ambient _ _ _ hp hn p).trans
    (point_point_ab k C c₀ hC ambient b c a s j l i tail
      (hp.perm p (fun h => maskDisjoint_symm h))
      (fun x hx => hn x (p.mem_iff.mpr hx)) hj hl hi)

/-- The same actual contraction in canonical target order. -/
theorem diagonal_diagonal_canonical (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,l) :: .inr (j,l) :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (CurvePowerGraphLocal.canonical ((a ||| b ||| c) :: s)) := by
  have ht := target_properties hp hn ((a ||| b ||| c) :: s) (by simp [targets])
  exact (diagonal_diagonal k C c₀ hC ambient a b c s i j l tail hp hn hi hj hl).trans
    (tautologicalFunctional_canonical k C c₀ ambient tail _ ht.1 ht.2).symm

/-- The same actual contraction in canonical target order. -/
theorem diagonal_point_ac_canonical (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,l) :: .inl j :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (CurvePowerGraphLocal.canonical ((a ||| c) :: s)) := by
  have ht := target_properties hp hn ((a ||| c) :: s) (by simp [targets])
  exact (diagonal_point_ac k C c₀ hC ambient a b c s i j l tail hp hn hi hj hl).trans
    (tautologicalFunctional_canonical k C c₀ ambient tail _ ht.1 ht.2).symm

/-- The same actual contraction in canonical target order. -/
theorem diagonal_point_bc_canonical (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (j,l) :: .inl i :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (CurvePowerGraphLocal.canonical ((b ||| c) :: s)) := by
  have ht := target_properties hp hn ((b ||| c) :: s) (by simp [targets])
  exact (diagonal_point_bc k C c₀ hC ambient a b c s i j l tail hp hn hi hj hl).trans
    (tautologicalFunctional_canonical k C c₀ ambient tail _ ht.1 ht.2).symm

/-- The same actual contraction in canonical target order. -/
theorem diagonal_point_ab_canonical (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: .inl l :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (CurvePowerGraphLocal.canonical ((a ||| b) :: s)) := by
  have ht := target_properties hp hn ((a ||| b) :: s) (by simp [targets])
  exact (diagonal_point_ab k C c₀ hC ambient a b c s i j l tail hp hn hi hj hl).trans
    (tautologicalFunctional_canonical k C c₀ ambient tail _ ht.1 ht.2).symm

/-- The same actual contraction in canonical target order. -/
theorem point_point_ab_canonical (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inl i :: .inl j :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (CurvePowerGraphLocal.canonical (c :: s)) := by
  have ht := target_properties hp hn (c :: s) (by simp [targets])
  exact (point_point_ab k C c₀ hC ambient a b c s i j l tail hp hn hi hj hl).trans
    (tautologicalFunctional_canonical k C c₀ ambient tail _ ht.1 ht.2).symm

/-- The same actual contraction in canonical target order. -/
theorem point_point_ac_canonical (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inl i :: .inl l :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (CurvePowerGraphLocal.canonical (b :: s)) := by
  have ht := target_properties hp hn (b :: s) (by simp [targets])
  exact (point_point_ac k C c₀ hC ambient a b c s i j l tail hp hn hi hj hl).trans
    (tautologicalFunctional_canonical k C c₀ ambient tail _ ht.1 ht.2).symm

/-- The same actual contraction in canonical target order. -/
theorem point_point_bc_canonical (ambient a b c : ℕ) (s : State)
    (i j l : Fin ambient) (tail : List (Letter ambient))
    (hp : (a :: b :: c :: s).Pairwise MaskDisjoint)
    (hn : ∀ x ∈ a :: b :: c :: s, x ≠ 0)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true)
    (hl : c.testBit l.val = true) :
    tautologicalFunctional k C c₀ ambient (.inl j :: .inl l :: tail)
        (a :: b :: c :: s) =
      tautologicalFunctional k C c₀ ambient tail (CurvePowerGraphLocal.canonical (a :: s)) := by
  have ht := target_properties hp hn (a :: s) (by simp [targets])
  exact (point_point_bc k C c₀ hC ambient a b c s i j l tail hp hn hi hj hl).trans
    (tautologicalFunctional_canonical k C c₀ ambient tail _ ht.1 ht.2).symm

end M9Native.CurvePowerThreeBlockWords

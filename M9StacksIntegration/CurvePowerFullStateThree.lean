module

public import M9StacksIntegration.CurvePowerFullState

/-! The whole original curve power with three selected distinct blocks
first. The state permutation is an actual coordinate isomorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurvePowerFullStateThree

open CurvePowerGraphLocal CurvePowerGraphMapReindex CurvePowerGraphDisjoint
open CurvePowerChowFunctional CurvePowerFullState

theorem bit_ne_of_fin_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) : bit i.val ≠ bit j.val := by
  intro he
  have ht : (bit i.val).testBit j.val = true := by
    rw [he]
    exact Nat.testBit_two_pow_self
  have hv : i.val = j.val := by
    simpa only [bit, Nat.testBit_two_pow, decide_eq_true_eq] using ht
  exact hij (Fin.ext hv)

def remaining (n : ℕ) (i j l : Fin n) : State :=
  (((fullState n).erase (bit i.val)).erase (bit j.val)).erase (bit l.val)

theorem fullState_perm_three (n : ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (fullState n).Perm (bit i.val :: bit j.val :: bit l.val :: remaining n i j l) := by
  have hab := bit_ne_of_fin_ne hij
  have hac := bit_ne_of_fin_ne hil
  have hbc := bit_ne_of_fin_ne hjl
  have hb : bit j.val ∈ (fullState n).erase (bit i.val) :=
    (List.mem_erase_of_ne (Ne.symm hab)).mpr (mem_fullState j)
  have hc : bit l.val ∈ ((fullState n).erase (bit i.val)).erase (bit j.val) :=
    (List.mem_erase_of_ne (Ne.symm hbc)).mpr
      ((List.mem_erase_of_ne (Ne.symm hac)).mpr (mem_fullState l))
  exact (List.perm_cons_erase (mem_fullState i)).trans
    (((List.perm_cons_erase hb).trans ((List.perm_cons_erase hc).cons (bit j.val))).cons
      (bit i.val))

theorem three_pairwise (n : ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (bit i.val :: bit j.val :: bit l.val :: remaining n i j l).Pairwise MaskDisjoint :=
  (fullState_pairwise n).perm (fullState_perm_three n i j l hij hil hjl)
    (fun h => maskDisjoint_symm h)

theorem three_nonzero (n : ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ∀ a ∈ (bit i.val :: bit j.val :: bit l.val :: remaining n i j l), a ≠ 0 := by
  intro a ha
  exact fullState_nonzero n a ((fullState_perm_three n i j l hij hil hjl).mem_iff.mpr ha)

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem actualWordDegree_three (n : ℕ) (i j l : Fin n)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (word : List (Letter n)) :
    CurvePowerPointTrace.actualWordDegree k C c₀ n word =
      tautologicalFunctional k C c₀ n word
        (bit i.val :: bit j.val :: bit l.val :: remaining n i j l) := by
  have hp := fullState_perm_three n i j l hij hil hjl
  have hpair := three_pairwise n i j l hij hil hjl
  have hn := three_nonzero n i j l hij hil hjl
  have hs := nodup_of_pairwise_nonzero _ hpair hn
  exact (tautologicalFunctional_fullState k C c₀ n word).symm.trans
    (CurvePowerPairingReindex.partitionFunctional_state_perm k C c₀ n
      (word.map (letterClass k C c₀ n)) (fullState n) _ (fullState_nodup n) hs
      (fullState_separated n) hp)

end M9Native.CurvePowerFullStateThree

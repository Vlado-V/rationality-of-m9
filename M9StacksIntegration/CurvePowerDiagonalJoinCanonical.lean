module

public import M9StacksIntegration.CurvePowerDiagonalJoinRestriction

/-!
# The actual diagonal join in canonical partition order

Disjoint nonzero blocks remain disjoint and nonzero after joining two
chosen blocks. The already-proved actual isomorphism comparison then
puts the joined partition in the literal order used by diagonalStep.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerDiagonalJoinCanonical

open CurvePowerGraphLocal CurvePowerGraphDisjoint CurvePowerGraphContexts
open CurvePowerChowFunctional

theorem joined_pairwise {s : State} (hs : s.Pairwise MaskDisjoint)
    (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ((a ||| b) :: (s.erase a).erase b).Pairwise MaskDisjoint := by
  have hbt : b ∈ s.erase a := (List.mem_erase_of_ne (Ne.symm hab)).mpr hb
  have hp : s.Perm (a :: b :: (s.erase a).erase b) :=
    (List.perm_cons_erase ha).trans ((List.perm_cons_erase hbt).cons a)
  have hf := hs.perm hp (fun h => maskDisjoint_symm h)
  rcases List.pairwise_cons.mp hf with ⟨hA, hBRest⟩
  rcases List.pairwise_cons.mp hBRest with ⟨hB, hRest⟩
  apply List.pairwise_cons.mpr
  exact ⟨fun c hc => maskDisjoint_or_left (hA c (List.mem_cons_of_mem b hc)) (hB c hc), hRest⟩

theorem joined_nonzero {s : State} (hs : ∀ c ∈ s, c ≠ 0)
    (a b : ℕ) (ha : a ∈ s) : ∀ c ∈ ((a ||| b) :: (s.erase a).erase b), c ≠ 0 := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · intro hz
    exact hs a ha (Nat.or_eq_zero_iff.mp hz).1
  · exact hs c (List.mem_of_mem_erase (List.mem_of_mem_erase hc))

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem tautologicalFunctional_canonical (ambient : ℕ) (word : List (Letter ambient))
    (s : State) (hp : s.Pairwise MaskDisjoint) (hn : ∀ c ∈ s, c ≠ 0) :
    tautologicalFunctional k C c₀ ambient word (canonical s) =
      tautologicalFunctional k C c₀ ambient word s := by
  have hs : s.Nodup := nodup_of_pairwise_nonzero s hp hn
  have ht : (canonical s).Nodup := (canonical_perm s).nodup_iff.mpr hs
  have hsep : CurvePowerGraphMapReindex.Separated s := separated_of_pairwise s hp
  exact (CurvePowerPairingReindex.partitionFunctional_state_perm k C c₀ ambient
    (word.map (letterClass k C c₀ ambient)) s (canonical s) hs ht hsep
      (canonical_perm s).symm).symm

theorem tautologicalFunctional_diagonal_free_blocks_canonical [IsAlgClosed k]
    [IsVariety k C.hom] (hC : topologicalKrullDim C.left = 1)
    (ambient : ℕ) (i j : Fin ambient) (tail : List (Letter ambient))
    (s : State) (hp : s.Pairwise MaskDisjoint) (hn : ∀ c ∈ s, c ≠ 0)
    (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hi : a.testBit i.val = true) (hj : b.testBit j.val = true) :
    tautologicalFunctional k C c₀ ambient (.inr (i,j) :: tail) s =
      tautologicalFunctional k C c₀ ambient tail
        (canonical ((a ||| b) :: (s.erase a).erase b)) := by
  have hs : s.Nodup := nodup_of_pairwise_nonzero s hp hn
  have hsep : CurvePowerGraphMapReindex.Separated s := separated_of_pairwise s hp
  have h := CurvePowerDiagonalJoinRestriction.tautologicalFunctional_diagonal_free_blocks
    k C c₀ hC ambient i j tail s hs hsep a b ha hb hab hi hj
  exact h.trans (tautologicalFunctional_canonical k C c₀ ambient tail _
    (joined_pairwise hp a b ha hb hab) (joined_nonzero hn a b ha)).symm

end M9Native.CurvePowerDiagonalJoinCanonical

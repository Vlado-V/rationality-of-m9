module

public import M9StacksIntegration.CurvePowerGraphMapRestrictions
public import M9StacksIntegration.CurvePowerGraphMapReindex

/-!
# Genuine restriction maps for a chosen block ordering

An actual finite-list permutation moves the chosen block(s) to the
front. Literal point insertion or coordinate doubling then realizes
pinning or joining those blocks. The map back to the original ordering
is constructed from the actual block-index equivalence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphBlockRestriction

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerGraphContexts
open CurvePowerGraphMapRestrictions CurvePowerGraphMapReindex

theorem separated_cons_disjoint (b : ℕ) (s : State) (hsep : Separated (b :: s))
    (v : ℕ) (hb : b.testBit v = true) : ∀ a ∈ s, a.testBit v = false := by
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ha
  apply Bool.eq_false_iff.mpr
  intro hj
  have he : (0 : Fin (b :: s).length) = j.succ := hsep v 0 j.succ hb hj
  have h := congrArg Fin.val he
  simp only [Fin.val_zero, Fin.val_succ] at h
  omega

variable {S : Scheme.{u}} (C : Over S) (c₀ : power C 0 ⟶ C)

def pinReindex (b : ℕ) (s t : State) (hs : (b :: s).Nodup) (ht : t.Nodup)
    (h : (b :: s).Perm t) : power C s.length ⟶ power C t.length :=
  insertConstant C c₀ s.length 0 ≫ reindex C (indexEquiv (b :: s) t hs ht h)

theorem pinReindex_stateMap (ambient b : ℕ) (s t : State) (hs : (b :: s).Nodup)
    (ht : t.Nodup) (hsep : Separated (b :: s)) (h : (b :: s).Perm t) :
    pinReindex C c₀ b s t hs ht h ≫ stateMap C c₀ ambient t = stateMap C c₀ ambient s := by
  rw [pinReindex, Category.assoc, stateMap_perm C c₀ ambient (b :: s) t hs ht hsep h]
  apply insertConstant_stateMap C c₀ ambient b s
  intro i hi
  exact separated_cons_disjoint b s hsep i.val hi

def joinReindex (a b : ℕ) (s t : State) (hs : (a :: b :: s).Nodup) (ht : t.Nodup)
    (h : (a :: b :: s).Perm t) : power C (s.length + 1) ⟶ power C t.length :=
  duplicateFirst C s.length ≫ reindex C (indexEquiv (a :: b :: s) t hs ht h)

theorem joinReindex_stateMap (ambient a b : ℕ) (s t : State) (hs : (a :: b :: s).Nodup)
    (ht : t.Nodup) (hsep : Separated (a :: b :: s)) (h : (a :: b :: s).Perm t) :
    joinReindex C a b s t hs ht h ≫ stateMap C c₀ ambient t =
      stateMap C c₀ ambient ((a ||| b) :: s) := by
  rw [joinReindex, Category.assoc, stateMap_perm C c₀ ambient (a :: b :: s) t hs ht hsep h]
  exact duplicateFirst_stateMap C c₀ ambient a b s

end M9Native.CurvePowerGraphBlockRestriction

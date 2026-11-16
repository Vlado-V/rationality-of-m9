module

public import M9StacksIntegration.CurvePowerGraphMaps
public import M9StacksIntegration.CurvePowerGraphContexts
public import Mathlib.Data.List.NodupEquivFin

/-!
# Genuine partition maps under reordering of blocks

The equivalence of block indices is constructed from the actual lists.
For separated blocks, the actual product reindexing composed with the
partition map is the partition map for the original ordering. This is
the geometric comparison required before applying the native invariance
of intersection numbers under a permutation of curve factors.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphMapReindex

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerGraphContexts

def Separated (s : State) : Prop :=
  ∀ (v : ℕ) (i j : Fin s.length), (s.get i).testBit v = true →
    (s.get j).testBit v = true → i = j

variable {S : Scheme.{u}} (C : Over S) (c₀ : power C 0 ⟶ C)

theorem stateCoordinate_eq_coord_of_unique (s : State) (hs : Separated s) (v : ℕ)
    (j : Fin s.length) (hj : (s.get j).testBit v = true) :
    stateCoordinate C c₀ s v = coord C s.length j := by
  apply stateCoordinate_eq_coord C c₀ s v j hj
  intro q hq
  apply Bool.eq_false_iff.mpr
  intro hh
  have he := hs v q j hh hj
  subst q
  exact Nat.lt_irrefl _ hq

theorem stateCoordinate_eq_fixed_of_get (s : State) (v : ℕ)
    (h : ∀ j : Fin s.length, (s.get j).testBit v = false) :
    stateCoordinate C c₀ s v = toUnit (power C s.length) ≫ c₀ := by
  exact stateCoordinate_eq_fixed C c₀ s v (List.forall_mem_iff_get.mpr h)

theorem separated_of_index_equiv (s t : State) (hs : Separated s)
    (e : Fin t.length ≃ Fin s.length) (he : ∀ j, t.get j = s.get (e j)) : Separated t := by
  intro v i j hi hj
  apply e.injective
  apply hs v (e i) (e j)
  · rw [← he]
    exact hi
  · rw [← he]
    exact hj

theorem reindex_stateCoordinate (s t : State) (hs : Separated s)
    (e : Fin t.length ≃ Fin s.length) (he : ∀ j, t.get j = s.get (e j)) (v : ℕ) :
    reindex C e ≫ stateCoordinate C c₀ t v = stateCoordinate C c₀ s v := by
  have ht := separated_of_index_equiv s t hs e he
  by_cases hv : ∃ j : Fin t.length, (t.get j).testBit v = true
  · obtain ⟨j, hj⟩ := hv
    have hj' : (s.get (e j)).testBit v = true := by rw [← he]; exact hj
    rw [stateCoordinate_eq_coord_of_unique C c₀ t ht v j hj,
      reindex_coord, stateCoordinate_eq_coord_of_unique C c₀ s hs v (e j) hj']
  · have htmiss : ∀ j : Fin t.length, (t.get j).testBit v = false := by
      intro j
      apply Bool.eq_false_iff.mpr
      exact fun h => hv ⟨j, h⟩
    have hsmiss : ∀ j : Fin s.length, (s.get j).testBit v = false := by
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      rw [← he]
      exact htmiss i
    rw [stateCoordinate_eq_fixed_of_get C c₀ t v htmiss,
      stateCoordinate_eq_fixed_of_get C c₀ s v hsmiss, ← Category.assoc]
    exact congrArg (fun f => f ≫ c₀) (toUnit_unique _ _)

theorem reindex_stateMap (ambient : ℕ) (s t : State) (hs : Separated s)
    (e : Fin t.length ≃ Fin s.length) (he : ∀ j, t.get j = s.get (e j)) :
    reindex C e ≫ stateMap C c₀ ambient t = stateMap C c₀ ambient s := by
  apply Stacks.CurvePower.hom_ext ambient
  intro i
  rw [Category.assoc, stateMap_coord, stateMap_coord]
  exact reindex_stateCoordinate C c₀ s t hs e he i.val

/-- Actual list-index equivalence, rather than an assumed coordinate permutation. -/
def indexEquiv (s t : State) (hs : s.Nodup) (ht : t.Nodup) (h : s.Perm t) :
    Fin t.length ≃ Fin s.length :=
  (List.Nodup.getEquiv t ht).trans
    ((Equiv.subtypeEquivRight (fun _a => h.mem_iff.symm)).trans
      (List.Nodup.getEquiv s hs).symm)

theorem get_indexEquiv (s t : State) (hs : s.Nodup) (ht : t.Nodup) (h : s.Perm t)
    (j : Fin t.length) : t.get j = s.get (indexEquiv s t hs ht h j) := by
  symm
  exact congrArg Subtype.val ((List.Nodup.getEquiv s hs).apply_symm_apply
    (Equiv.subtypeEquivRight (fun _a => h.mem_iff.symm) (List.Nodup.getEquiv t ht j)))

theorem stateMap_perm (ambient : ℕ) (s t : State) (hs : s.Nodup) (ht : t.Nodup)
    (hsep : Separated s) (h : s.Perm t) :
    reindex C (indexEquiv s t hs ht h) ≫ stateMap C c₀ ambient t =
      stateMap C c₀ ambient s :=
  reindex_stateMap C c₀ ambient s t hsep (indexEquiv s t hs ht h)
    (get_indexEquiv s t hs ht h)

end M9Native.CurvePowerGraphMapReindex

module

public import M9StacksIntegration.MukaiFourCircuitPair
public import M9StacksIntegration.MukaiFourCircuitPlanes
public import M9StacksIntegration.MukaiFourCircuitRelation

/-!
# A minimal four-point circuit has an actual common support line

The inputs are actual independent triples in the original six-dimensional
space, literal linear independence of every three exterior volumes, and
three-dimensional full volume span. The output is a genuine nonzero vector
in all four literal tuple spans.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open Module
open scoped BigOperators

namespace M9Native.MukaiFourCircuit
variable (K : Type*) [Field K]

/-- The actual nonzero relation and separated support planes already
force a common nonzero vector. -/
theorem exists_common_of_relation (h2 : (2 : K) ≠ 0)
    (u : Fin 4 → Fin 3 → Six K) (hu : ∀ i, LinearIndependent K (u i))
    (a : Fin 4 → K) (ha : ∀ i, a i ≠ 0)
    (hrel : ∑ i, a i • triple K (u i) = 0)
    (hplane : ∀ i j, i ≠ j → plane K (u i) ≠ plane K (u j)) :
    ∃ x : Six K, x ≠ 0 ∧ ∀ i, x ∈ plane K (u i) := by
  classical
  have hrelE (e : Equiv.Perm (Fin 4)) :
      a (e 0) • triple K (u (e 0)) + a (e 1) • triple K (u (e 1)) +
        a (e 2) • triple K (u (e 2)) + a (e 3) • triple K (u (e 3)) = 0 := by
    have hs : ∑ i : Fin 4, a (e i) • triple K (u (e i)) = 0 := by
      rw [Equiv.sum_comp e (fun i => a i • triple K (u i))]
      exact hrel
    simpa only [Fin.sum_univ_four] using hs
  have hno (i j : Fin 4) (hij : i ≠ j) :
      ¬ Disjoint (plane K (u i)) (plane K (u j)) := by
    obtain ⟨e, he0, he1⟩ := exists_perm_pair i j hij
    have hn := not_disjoint_of_relation K h2 (u (e 0)) (u (e 1)) (u (e 2)) (u (e 3))
      (hu (e 0)) (hu (e 1)) (hu (e 2))
      (a (e 0)) (a (e 1)) (a (e 2)) (a (e 3))
      (ha (e 0)) (ha (e 1)) (ha (e 2)) (ha (e 3)) (hrelE e)
      (hplane (e 2) (e 0) (e.injective.ne (by decide)))
      (hplane (e 2) (e 1) (e.injective.ne (by decide)))
    simpa only [he0, he1] using hn
  by_contra hncommon
  have hnotone (i j : Fin 4) (hij : i ≠ j) :
      finrank K ↥(plane K (u i) ⊓ plane K (u j)) ≠ 1 := by
    intro hone
    obtain ⟨e, he0, he1⟩ := exists_perm_pair i j hij
    have hone' : finrank K ↥(plane K (u (e 0)) ⊓ plane K (u (e 1))) = 1 := by
      rw [he0, he1]
      exact hone
    obtain ⟨x, hnx, hx0, hx1, hx2, hx3⟩ := exists_common_of_pair_inf_one K
      (u (e 0)) (u (e 1)) (u (e 2)) (u (e 3))
      (hu (e 0)) (hu (e 1)) (hu (e 2)) (hu (e 3))
      (a (e 0)) (a (e 1)) (a (e 2)) (a (e 3))
      (ha (e 0)) (ha (e 1)) (hrelE e) hone'
      (hno (e 2) (e 3) (e.injective.ne (by decide)))
    apply hncommon
    refine ⟨x, hnx, ?_⟩
    intro k
    obtain ⟨l, rfl⟩ := e.surjective k
    fin_cases l
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
  have hpair (i j : Fin 4) :
      2 ≤ finrank K ↥(plane K (u i) ⊓ plane K (u j)) := by
    by_cases hij : i = j
    · subst j
      have hm := Submodule.finrank_mono (show plane K (u i) ≤
        plane K (u i) ⊓ plane K (u i) from le_inf le_rfl le_rfl)
      have hd := plane_finrank K (u i) (hu i)
      omega
    · have hne : plane K (u i) ⊓ plane K (u j) ≠ ⊥ := by
        simpa only [disjoint_iff, le_bot_iff] using hno i j hij
      have hp : 1 ≤ finrank K ↥(plane K (u i) ⊓ plane K (u j)) :=
        Submodule.one_le_finrank_iff.mpr hne
      have hn := hnotone i j hij
      omega
  have h01 : finrank K ↥(plane K (u 0) ⊓ plane K (u 1)) = 2 := by
    have hproper : plane K (u 0) ⊓ plane K (u 1) < plane K (u 0) := by
      apply lt_of_le_of_ne inf_le_left
      intro he
      have hle : plane K (u 0) ≤ plane K (u 1) := by
        rw [← he]
        exact inf_le_right
      have heq := Submodule.eq_of_le_of_finrank_eq hle
        ((plane_finrank K (u 0) (hu 0)).trans (plane_finrank K (u 1) (hu 1)).symm)
      exact hplane 0 1 (by decide) heq
    have hlt := Submodule.finrank_lt_finrank_of_lt hproper
    rw [plane_finrank K (u 0) (hu 0)] at hlt
    have hp := hpair 0 1
    omega
  rcases common_or_contained_four K (fun i => plane K (u i))
      (fun i => plane_finrank K (u i) (hu i)) hpair h01 with hc | ⟨S, hS, hinc⟩
  · exact hncommon hc
  · apply hncommon
    apply exists_common_of_contained_four K u hu S hS hinc a (ha 3)
    simpa only [Fin.sum_univ_four] using hrel

/-- Minimal four-point Grassmannian circuits in the actual exterior cube
have a genuine common nonzero support vector. -/
theorem exists_nonzero_mem_all_planes (h2 : (2 : K) ≠ 0)
    (u : Fin 4 → Fin 3 → Six K) (hu : ∀ i, LinearIndependent K (u i))
    (hthree : EveryThreeLI K (fun i => triple K (u i)))
    (hrank : finrank K ↥(Submodule.span K (Set.range (fun i => triple K (u i)))) = 3) :
    ∃ x : Six K, x ≠ 0 ∧ ∀ i, x ∈ plane K (u i) := by
  obtain ⟨a, ha, hrel⟩ := exists_relation_all_ne_zero K (fun i => triple K (u i)) hthree
    (dependent_of_span_finrank_three K (fun i => triple K (u i)) hrank)
  exact exists_common_of_relation K h2 u hu a ha hrel (plane_ne_of_everyThreeLI K u hu hthree)

/-- Literal native-coordinate interface, with no abbreviation for the
exterior carrier, tuple planes, or every-three deletion condition. -/
theorem exists_nonzero_mem_all_actual_planes (h2 : (2 : K) ≠ 0)
    (u : Fin 4 → Fin 3 → Fin 6 → K) (hu : ∀ i, LinearIndependent K (u i))
    (hthree : ∀ j : Fin 4, LinearIndependent K
      (j.removeNth (fun i => exteriorPower.ιMulti K 3 (u i))))
    (hrank : finrank K ↥(Submodule.span K
      (Set.range (fun i => exteriorPower.ιMulti K 3 (u i)))) = 3) :
    ∃ x : Fin 6 → K, x ≠ 0 ∧ ∀ i, x ∈ Submodule.span K (Set.range (u i)) :=
  exists_nonzero_mem_all_planes K h2 u hu hthree hrank

end M9Native.MukaiFourCircuit

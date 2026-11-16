module

public import M9StacksIntegration.MukaiFourCircuitBasic
public import M9StacksIntegration.MukaiFourCircuitDisjoint

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open Module
open scoped BigOperators

namespace M9Native.MukaiFourCircuit
variable (K : Type*) [Field K]

/-- Every injective subfamily of length below four inherits literal
linear independence from the deletion condition. -/
theorem EveryThreeLI.comp {z : Fin 4 → Three K} (hz : EveryThreeLI K z)
    {n : ℕ} (f : Fin n → Fin 4) (hf : Function.Injective f) (hn : n < 4) :
    LinearIndependent K (z ∘ f) := by
  classical
  have hns : ¬ Function.Surjective f := by
    intro hs
    have hc := Fintype.card_le_of_surjective f hs
    simp only [Fintype.card_fin] at hc
    omega
  change ¬ (∀ y, ∃ x, f x = y) at hns
  push Not at hns
  obtain ⟨j, hj⟩ := hns
  have hp : ∀ i, ∃ k : Fin 3, j.succAbove k = f i :=
    fun i => Fin.exists_succAbove_eq (hj i)
  choose g hg using hp
  have hgI : Function.Injective g := by
    intro i k hik
    apply hf
    rw [← hg i, ← hg k, hik]
  have h := (hz j).comp g hgI
  simpa only [Fin.removeNth, Function.comp_def, hg] using h

/-- A minimal dependence has no zero coefficient, with no desired
normalization supplied as an assumption. -/
theorem exists_relation_all_ne_zero (z : Fin 4 → Three K)
    (hz : EveryThreeLI K z) (hd : ¬ LinearIndependent K z) :
    ∃ a : Fin 4 → K, (∀ i, a i ≠ 0) ∧ ∑ i, a i • z i = 0 := by
  obtain ⟨a, hsum, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hd
  refine ⟨a, ?_, hsum⟩
  intro j hj
  have hsum' : ∑ i : Fin 3, a (j.succAbove i) • z (j.succAbove i) = 0 := by
    have he := Fin.sum_univ_succAbove (fun i : Fin 4 => a i • z i) j
    rw [he, hj, zero_smul, zero_add] at hsum
    exact hsum
  have ha := Fintype.linearIndependent_iff.mp (hz j) (j.removeNth a) hsum'
  have hall : ∀ i, a i = 0 := j.forall_iff_succAbove.mpr ⟨hj, ha⟩
  exact hk (hall k)

/-- Scaling one slot realizes any nonzero volume scalar in the original
actual three-plane. -/
def scaleTuple (a : K) (s : Fin 3 → Six K) : Fin 3 → Six K :=
  Function.update s 0 (a • s 0)

@[simp] theorem triple_scaleTuple (a : K) (s : Fin 3 → Six K) :
    triple K (scaleTuple K a s) = a • triple K s := by
  simpa only [triple, scaleTuple, Function.update_eq_self] using
    (exteriorPower.ιMulti K 3).map_update_smul s 0 a (s 0)

theorem linearIndependent_scaleTuple (a : K) (ha : a ≠ 0)
    (s : Fin 3 → Six K) (hs : LinearIndependent K s) :
    LinearIndependent K (scaleTuple K a s) := by
  classical
  have h := hs.units_smul (fun i => if i = 0 then Units.mk0 a ha else 1)
  convert h using 1
  funext i
  by_cases hi : i = 0 <;> simp [scaleTuple, hi, Pi.smul_apply', Units.smul_def]

@[simp] theorem plane_scaleTuple (a : K) (ha : a ≠ 0)
    (s : Fin 3 → Six K) (hs : LinearIndependent K s) :
    plane K (scaleTuple K a s) = plane K s := by
  exact span_eq_of_smul_ιMulti_eq K (scaleTuple K a s) s
    (linearIndependent_scaleTuple K a ha s hs) hs 1 a one_ne_zero ha
    (by
      change 1 • triple K (scaleTuple K a s) = a • triple K s
      rw [one_smul, triple_scaleTuple])

theorem linearIndependent_append_of_disjoint (s t : Fin 3 → Six K)
    (hs : LinearIndependent K s) (ht : LinearIndependent K t)
    (hd : Disjoint (plane K s) (plane K t)) :
    LinearIndependent K (Fin.append s t) := by
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  have h := (hs.sum_type ht hd).comp e.symm e.symm.injective
  convert h using 1
  funext i
  fin_cases i <;> rfl

/-- A genuine four-term circuit cannot have disjoint first supports. -/
theorem not_disjoint_of_relation (h2 : (2 : K) ≠ 0)
    (s t u v : Fin 3 → Six K)
    (hs : LinearIndependent K s) (ht : LinearIndependent K t)
    (hu : LinearIndependent K u)
    (a b c d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hrel : a • triple K s + b • triple K t + c • triple K u + d • triple K v = 0)
    (hus : plane K u ≠ plane K s) (hut : plane K u ≠ plane K t) :
    ¬ Disjoint (plane K s) (plane K t) := by
  intro hdisj
  let s' := scaleTuple K a s
  let t' := scaleTuple K b t
  let u' := scaleTuple K (-c) u
  let v' := scaleTuple K (-d) v
  have hs' := linearIndependent_scaleTuple K a ha s hs
  have ht' := linearIndependent_scaleTuple K b hb t ht
  have hu' := linearIndependent_scaleTuple K (-c) (neg_ne_zero.mpr hc) u hu
  have hdisj' : Disjoint (plane K s') (plane K t') := by
    simpa only [s', t', plane_scaleTuple K a ha s hs, plane_scaleTuple K b hb t ht] using hdisj
  have happ := linearIndependent_append_of_disjoint K s' t' hs' ht' hdisj'
  have hsum : exteriorPower.ιMulti K 3 s' + exteriorPower.ιMulti K 3 t' =
      exteriorPower.ιMulti K 3 u' + exteriorPower.ιMulti K 3 v' := by
    change triple K s' + triple K t' = triple K u' + triple K v'
    simp only [s', t', u', v', triple_scaleTuple]
    have he : (a • triple K s + b • triple K t) +
        (c • triple K u + d • triple K v) = 0 := by
      simpa only [add_assoc] using hrel
    rw [neg_smul c (triple K u), neg_smul d (triple K v), ← neg_add]
    exact eq_neg_of_add_eq_zero_left he
  have hp := MukaiFourCircuitDisjoint.span_eq_or_span_eq_of_disjoint_sum K h2
    s' t' u' v' happ hu' hsum
  change plane K u' = plane K s' ∨ plane K u' = plane K t' at hp
  simp only [u', s', t', plane_scaleTuple K (-c) (neg_ne_zero.mpr hc) u hu,
    plane_scaleTuple K a ha s hs, plane_scaleTuple K b hb t ht] at hp
  exact hp.elim hus hut

/-- Literal every-three independence separates the actual tuple planes. -/
theorem plane_ne_of_everyThreeLI (u : Fin 4 → Fin 3 → Six K)
    (hu : ∀ i, LinearIndependent K (u i))
    (hz : EveryThreeLI K (fun i => triple K (u i)))
    (i j : Fin 4) (hij : i ≠ j) : plane K (u i) ≠ plane K (u j) := by
  intro he
  have hpair : LinearIndependent K ![triple K (u i), triple K (u j)] := by
    have hf : Function.Injective (![i,j] : Fin 2 → Fin 4) := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    convert hz.comp K ![i,j] hf (by decide) using 1
    funext k
    fin_cases k <;> rfl
  obtain ⟨c, hc⟩ := exists_triple_smul_of_mem_plane K (u i) (u j) (hu i) (by
    intro k
    rw [he]
    exact Submodule.subset_span ⟨k, rfl⟩)
  have hn := (LinearIndependent.pair_iff' (ιMulti_ne_zero K (u i) (hu i))).mp hpair c
  exact hn hc.symm

/-- Reordering a circuit can place any two distinct actual supports first. -/
theorem exists_perm_pair (i j : Fin 4) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin 4), e 0 = i ∧ e 1 = j := by
  classical
  let e₀ : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  let k := e₀ j
  have hk : k ≠ 0 := by
    intro h
    have he := congrArg e₀ h
    have hji : j = i := by simpa only [k, e₀, Equiv.swap_apply_self, Equiv.swap_apply_left] using he
    exact hij hji.symm
  let e := (Equiv.swap 1 k).trans e₀
  refine ⟨e, ?_, ?_⟩
  · change e₀ ((Equiv.swap 1 k) 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) hk.symm]
    simp only [e₀, Equiv.swap_apply_left]
  · change e₀ ((Equiv.swap 1 k) 1) = j
    rw [Equiv.swap_apply_left]
    simp only [k, e₀, Equiv.swap_apply_self]

end M9Native.MukaiFourCircuit

module

public import M9StacksIntegration.MukaiFourCircuitBasic

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open Module

namespace M9Native.MukaiFourCircuit
variable (K : Type*) [Field K]

/-- Elementary geometry of pairwise adjacent three-planes. -/
theorem inf_sup_eq_inf_of_not_le {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A B C : Submodule K V)
    (hC : finrank K C = 3) (hAB : finrank K ↥(A ⊓ B) = 2)
    (hCA : 2 ≤ finrank K ↥(C ⊓ A)) (hCB : 2 ≤ finrank K ↥(C ⊓ B))
    (hn : ¬ C ≤ A ⊔ B) : C ⊓ (A ⊔ B) = A ⊓ B := by
  let T := C ⊓ (A ⊔ B)
  have hproper : T < C := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    apply hn
    rw [← he]
    exact inf_le_right
  have hlt : finrank K T < 3 := (Submodule.finrank_lt_finrank_of_lt hproper).trans_eq hC
  have hCAle : C ⊓ A ≤ T := inf_le_inf_left C le_sup_left
  have hCBle : C ⊓ B ≤ T := inf_le_inf_left C le_sup_right
  have hdim : finrank K T = 2 := by
    have hm := Submodule.finrank_mono hCAle
    omega
  have hCAeq : C ⊓ A = T := Submodule.eq_of_le_of_finrank_eq hCAle (by
    have hm := Submodule.finrank_mono hCAle
    omega)
  have hCBeq : C ⊓ B = T := Submodule.eq_of_le_of_finrank_eq hCBle (by
    have hm := Submodule.finrank_mono hCBle
    omega)
  have hTU : T ≤ A ⊓ B := le_inf
    (hCAeq ▸ inf_le_right) (hCBeq ▸ inf_le_right)
  exact Submodule.eq_of_le_of_finrank_eq hTU (hdim.trans hAB.symm)

/-- Four pairwise adjacent three-planes either already share a nonzero
vector, or are all contained in one actual four-dimensional subspace. -/
theorem common_or_contained_four (P : Fin 4 → Submodule K (Six K))
    (hrank : ∀ i, finrank K (P i) = 3)
    (hpair : ∀ i j, 2 ≤ finrank K ↥(P i ⊓ P j))
    (h01 : finrank K ↥(P 0 ⊓ P 1) = 2) :
    (∃ x : Six K, x ≠ 0 ∧ ∀ i, x ∈ P i) ∨
      (∃ S : Submodule K (Six K), finrank K S = 4 ∧ ∀ i, P i ≤ S) := by
  classical
  let S := P 0 ⊔ P 1
  have hS : finrank K S = 4 := by
    change finrank K ↥(P 0 ⊔ P 1) = 4
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (P 0) (P 1)
    rw [hrank 0, hrank 1, h01] at hd
    omega
  by_cases hall : ∀ i, P i ≤ S
  · exact Or.inr ⟨S, hS, hall⟩
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    let U := P 0 ⊓ P 1
    have hkU : P k ⊓ S = U := inf_sup_eq_inf_of_not_le K (P 0) (P 1) (P k)
      (hrank k) h01 (hpair k 0) (hpair k 1) hk
    have hUall : ∀ i, U ≤ P i := by
      intro i
      by_cases hi : P i ≤ S
      · have hle : P k ⊓ P i ≤ U := by
          rw [← hkU]
          exact inf_le_inf_left (P k) hi
        have he : P k ⊓ P i = U := Submodule.eq_of_le_of_finrank_eq hle (by
          have hm := Submodule.finrank_mono hle
          have hp := hpair k i
          change finrank K U = 2 at h01
          omega)
        rw [← he]
        exact inf_le_right
      · have hiU := inf_sup_eq_inf_of_not_le K (P 0) (P 1) (P i)
          (hrank i) h01 (hpair i 0) (hpair i 1) hi
        change P i ⊓ S = U at hiU
        rw [← hiU]
        exact inf_le_left
    have hUne : U ≠ ⊥ := by
      intro he
      change finrank K U = 2 at h01
      rw [he, finrank_bot] at h01
      omega
    obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    exact Or.inl ⟨x, hn, fun i => hUall i hx⟩

/-- Actual exterior multiplication with a fixed independent triple tail. -/
def consWedge {V : Type*} [AddCommGroup V] [Module K V] (s : Fin 3 → V) :
    V →ₗ[K] ⋀[K]^4 V where
  toFun x := exteriorPower.ιMulti K 4 (Fin.cons x s)
  map_add' x y := (exteriorPower.ιMulti K 4).map_vecCons_add s x y
  map_smul' c x := (exteriorPower.ιMulti K 4).map_vecCons_smul s c x

/-- Inside a genuine four-dimensional ambient space, a four-term volume
relation forces an actual common nonzero vector by rank-nullity. -/
theorem exists_common_of_contained_four (u : Fin 4 → Fin 3 → Six K)
    (hu : ∀ i, LinearIndependent K (u i))
    (S : Submodule K (Six K)) (hS : finrank K S = 4)
    (hinc : ∀ i, plane K (u i) ≤ S)
    (a : Fin 4 → K) (ha3 : a 3 ≠ 0)
    (hrel : a 0 • triple K (u 0) + a 1 • triple K (u 1) +
      a 2 • triple K (u 2) + a 3 • triple K (u 3) = 0) :
    ∃ x : Six K, x ≠ 0 ∧ ∀ i, x ∈ plane K (u i) := by
  let u' : Fin 4 → Fin 3 → S := fun i j =>
    ⟨u i j, hinc i (Submodule.subset_span ⟨j, rfl⟩)⟩
  let F : S →ₗ[K] (Fin 3 → ⋀[K]^4 S) :=
    LinearMap.pi fun i => consWedge K (u' i.castSucc)
  have htarget : finrank K (Fin 3 → ⋀[K]^4 S) = 3 := by
    rw [Module.finrank_pi_fintype]
    simp only [exteriorPower.finrank_eq, hS]
    norm_num
  have hker : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [htarget, hS]
    omega)
  obtain ⟨x, hx, hnx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hfirst : ∀ i : Fin 3, x.val ∈ plane K (u i.castSucc) := by
    intro i
    have hi : exteriorPower.ιMulti K 4 (Fin.cons x (u' i.castSucc)) = 0 :=
      congrFun hx i
    have hi' := congrArg (exteriorPower.map 4 S.subtype) hi
    rw [map_zero, exteriorPower.map_apply_ιMulti] at hi'
    have hz : ExteriorAlgebra.ι K x.val * ExteriorAlgebra.ιMulti K 3 (u i.castSucc) = 0 := by
      rw [show ExteriorAlgebra.ι K x.val * ExteriorAlgebra.ιMulti K 3 (u i.castSucc) =
        ExteriorAlgebra.ιMulti K 4 (Fin.cons x.val (u i.castSucc)) from
        (ExteriorAlgebra.ιMulti_succ_apply (R := K) (Fin.cons x.val (u i.castSucc))).symm]
      exact congrArg Subtype.val hi'
    exact (ι_mul_ιMulti_eq_zero_iff K (u i.castSucc) (hu i.castSucc) x.val).mp hz
  have hzfirst : ∀ i : Fin 3,
      ExteriorAlgebra.ι K x.val * (triple K (u i.castSucc)).val = 0 := by
    intro i
    exact (ι_mul_ιMulti_eq_zero_iff K (u i.castSucc) (hu i.castSucc) x.val).mpr (hfirst i)
  have hz0 : ExteriorAlgebra.ι K x.val * (triple K (u 0)).val = 0 := hzfirst 0
  have hz1 : ExteriorAlgebra.ι K x.val * (triple K (u 1)).val = 0 := hzfirst 1
  have hz2 : ExteriorAlgebra.ι K x.val * (triple K (u 2)).val = 0 := hzfirst 2
  have hlast : x.val ∈ plane K (u 3) := by
    have he := congrArg (fun z : Three K => ExteriorAlgebra.ι K x.val * z.val) hrel
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero, mul_zero] at he
    change ExteriorAlgebra.ι K x.val *
      (a 0 • (triple K (u 0)).val + a 1 • (triple K (u 1)).val +
        a 2 • (triple K (u 2)).val + a 3 • (triple K (u 3)).val) = 0 at he
    simp only [mul_add, mul_smul_comm, hz0, hz1, hz2, smul_zero, zero_add] at he
    have hz : ExteriorAlgebra.ι K x.val * (triple K (u 3)).val = 0 :=
      (smul_eq_zero.mp he).resolve_left ha3
    exact (ι_mul_ιMulti_eq_zero_iff K (u 3) (hu 3) x.val).mp hz
  refine ⟨x.val, (fun h => hnx (Subtype.ext h)), ?_⟩
  intro i
  fin_cases i
  · exact hfirst 0
  · exact hfirst 1
  · exact hfirst 2
  · exact hlast

end M9Native.MukaiFourCircuit

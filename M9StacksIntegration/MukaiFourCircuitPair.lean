module

public import M9StacksIntegration.MukaiFourCircuitBasic

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open Module

namespace M9Native.MukaiFourCircuit
variable (K : Type*) [Field K]

/-- The common vectors of two supports annihilate every weighted sum. -/
theorem inf_plane_le_wedgeAnn_sum (s t : Fin 3 → Six K)
    (hs : LinearIndependent K s) (ht : LinearIndependent K t) (a b : K) :
    plane K s ⊓ plane K t ≤ wedgeAnn K (a • triple K s + b • triple K t) := by
  intro x hx
  have hsx := (mem_wedgeAnn K (triple K s) x).mp ((wedgeAnn_triple_eq_plane K s hs).symm ▸ hx.1)
  have htx := (mem_wedgeAnn K (triple K t) x).mp ((wedgeAnn_triple_eq_plane K t ht).symm ▸ hx.2)
  change ExteriorAlgebra.ι K x * (a • (triple K s).val + b • (triple K t).val) = 0
  simp only [mul_add, mul_smul_comm, hsx, htx, smul_zero, add_zero]

/-- If the two support planes span at least five dimensions, the intrinsic
annihilator of their weighted sum is exactly their actual intersection. -/
theorem wedgeAnn_sum_eq_inf_of_four_lt (s t : Fin 3 → Six K)
    (hs : LinearIndependent K s) (ht : LinearIndependent K t)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hlarge : 4 < finrank K ↥(plane K s ⊔ plane K t)) :
    wedgeAnn K (a • triple K s + b • triple K t) = plane K s ⊓ plane K t := by
  apply le_antisymm ?_ (inf_plane_le_wedgeAnn_sum K s t hs ht a b)
  intro x hx
  have hprod (r : Fin 3 → Six K) :
      ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K 3 r =
        ExteriorAlgebra.ιMulti K 4 (Fin.cons x r) :=
    (ExteriorAlgebra.ιMulti_succ_apply (R := K) (Fin.cons x r)).symm
  have hsum : a • ExteriorAlgebra.ιMulti K 4 (Fin.cons x s) +
      b • ExteriorAlgebra.ιMulti K 4 (Fin.cons x t) = 0 := by
    change ExteriorAlgebra.ι K x *
      (a • ExteriorAlgebra.ιMulti K 3 s + b • ExteriorAlgebra.ιMulti K 3 t) = 0 at hx
    simpa only [mul_add, mul_smul_comm, hprod] using hx
  have heq : a • exteriorPower.ιMulti K 4 (Fin.cons x s) =
      (-b) • exteriorPower.ιMulti K 4 (Fin.cons x t) := by
    apply Subtype.ext
    change a • ExteriorAlgebra.ιMulti K 4 (Fin.cons x s) =
      (-b) • ExteriorAlgebra.ιMulti K 4 (Fin.cons x t)
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hsum
  have hzero : ExteriorAlgebra.ιMulti K 4 (Fin.cons x s) = 0 ↔
      ExteriorAlgebra.ιMulti K 4 (Fin.cons x t) = 0 := by
    have he := congrArg Subtype.val heq
    change a • ExteriorAlgebra.ιMulti K 4 (Fin.cons x s) =
      (-b) • ExteriorAlgebra.ιMulti K 4 (Fin.cons x t) at he
    have hz := congrArg (fun z : ExteriorAlgebra K (Six K) => z = 0) he
    simpa only [Submodule.coe_smul, smul_eq_zero, ha, neg_ne_zero.mpr hb, false_or] using Iff.of_eq hz
  have hmem : x ∈ plane K s ↔ x ∈ plane K t := by
    change x ∈ Submodule.span K (Set.range s) ↔ x ∈ Submodule.span K (Set.range t)
    rw [← ι_mul_ιMulti_eq_zero_iff K s hs, ← ι_mul_ιMulti_eq_zero_iff K t ht,
      hprod, hprod]
    exact hzero
  have hxs : x ∈ plane K s := by
    by_contra hn
    have hsc := hs.finCons hn
    have htc := ht.finCons (fun h => hn (hmem.mpr h))
    have hspan := span_eq_of_smul_ιMulti_eq K (Fin.cons x s) (Fin.cons x t)
      hsc htc a (-b) ha (neg_ne_zero.mpr hb) heq
    let P := Submodule.span K (Set.range (Fin.cons x s))
    have hsP : plane K s ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.succ, rfl⟩
    have htP : plane K t ≤ P := by
      change plane K t ≤ Submodule.span K (Set.range (Fin.cons x s))
      rw [hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.succ, rfl⟩
    have hdim := Submodule.finrank_mono (sup_le hsP htP)
    have hP : finrank K P = 4 := by
      simpa only [P, Fintype.card_fin] using finrank_span_eq_card hsc
    omega
  exact ⟨hxs, hmem.mp hxs⟩

/-- An actual one-dimensional pair intersection is the intrinsic common
line for any four-term relation with nonzero coefficients. -/
theorem exists_common_of_pair_inf_one (s t u v : Fin 3 → Six K)
    (hs : LinearIndependent K s) (ht : LinearIndependent K t)
    (hu : LinearIndependent K u) (hv : LinearIndependent K v)
    (a b c d : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrel : a • triple K s + b • triple K t + c • triple K u + d • triple K v = 0)
    (hone : finrank K ↥(plane K s ⊓ plane K t) = 1)
    (hother : ¬ Disjoint (plane K u) (plane K v)) :
    ∃ x : Six K, x ≠ 0 ∧ x ∈ plane K s ∧ x ∈ plane K t ∧
      x ∈ plane K u ∧ x ∈ plane K v := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (plane K s) (plane K t)
  rw [plane_finrank K s hs, plane_finrank K t ht, hone] at hdim
  have hann := wedgeAnn_sum_eq_inf_of_four_lt K s t hs ht a b ha hb (by omega)
  have hne : plane K u ⊓ plane K v ≠ ⊥ := by
    simpa only [disjoint_iff, le_bot_iff] using hother
  obtain ⟨x, hx, hnx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxann : x ∈ wedgeAnn K (c • triple K u + d • triple K v) :=
    inf_plane_le_wedgeAnn_sum K u v hu hv c d hx
  have hzero := congrArg (fun z : Three K => ExteriorAlgebra.ι K x * z.val) hrel
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero, mul_zero] at hzero
  have hxw : x ∈ wedgeAnn K (a • triple K s + b • triple K t) := by
    change ExteriorAlgebra.ι K x * (a • (triple K s).val + b • (triple K t).val) = 0
    change ExteriorAlgebra.ι K x * (c • (triple K u).val + d • (triple K v).val) = 0 at hxann
    change ExteriorAlgebra.ι K x *
      (a • (triple K s).val + b • (triple K t).val +
        c • (triple K u).val + d • (triple K v).val) = 0 at hzero
    rw [show a • (triple K s).val + b • (triple K t).val +
        c • (triple K u).val + d • (triple K v).val =
      (a • (triple K s).val + b • (triple K t).val) +
        (c • (triple K u).val + d • (triple K v).val) by abel,
      mul_add, hxann, add_zero] at hzero
    exact hzero
  rw [hann] at hxw
  exact ⟨x, hnx, hxw.1, hxw.2, hx.1, hx.2⟩

end M9Native.MukaiFourCircuit

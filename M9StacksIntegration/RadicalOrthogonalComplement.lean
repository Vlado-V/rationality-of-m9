module

public import M9.RadicalFiber

/-!
# A radical line in the orthogonal complement of a nondegenerate four-plane

For an actual nonzero vector orthogonal to an actual nondegenerate
subspace, adjoining its line has exactly that line as radical. Actual
orthogonal complementation preserves this radical. In ambient dimension
fourteen and subspace dimension four, the resulting complement is an
actual nine-plane. All conclusions are proved from the actual form;
there is no radical or dimension premise for the output subspace.
-/

@[expose] public noncomputable section

namespace M9.RadicalFiber

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem radical_orthogonal_eq (B : LinearMap.BilinForm K V)
    (hB : B.IsAlt) (hND : B.Nondegenerate) (S : Submodule K V) :
    radical B (B.orthogonal S) = radical B S := by
  unfold radical
  rw [B.orthogonal_orthogonal hND hB.isRefl S,inf_comm]

theorem radical_line_sup_of_nondegenerate (B : LinearMap.BilinForm K V)
    (hB : B.IsAlt) (ρ : V) (hρ : ρ ≠ 0) (U : Submodule K V)
    (hU : (B.restrict U).Nondegenerate) (hρU : ρ ∈ B.orthogonal U) :
    radical B ((K ∙ ρ) ⊔ U) = K ∙ ρ := by
  have hL : (K ∙ ρ) ≤ B.orthogonal U :=
    (Submodule.span_singleton_le_iff_mem ρ (B.orthogonal U)).mpr hρU
  have hLi : (K ∙ ρ) ≤ B.orthogonal (K ∙ ρ) :=
    line_isotropic B hB _ (finrank_span_singleton hρ)
  have hrU : radical B U = ⊥ := (radical_eq_bot_iff B hB.isRefl U).2 hU
  apply le_antisymm
  · rintro x ⟨hx,hxo⟩
    obtain ⟨l,hl,u,hu,rfl⟩ := Submodule.mem_sup.mp hx
    have huo : u ∈ B.orthogonal U := by
      intro v hv
      have hx := hxo v ((le_sup_right : U ≤ (K ∙ ρ) ⊔ U) hv)
      have hlv := hL hl v hv
      simpa only [map_add,hlv,zero_add] using hx
    have hu0 : u = 0 := by
      have hmem : u ∈ radical B U := ⟨hu,huo⟩
      simpa only [hrU,Submodule.mem_bot] using hmem
    simpa only [hu0,add_zero] using hl
  · intro l hl
    refine ⟨(le_sup_left : (K ∙ ρ) ≤ (K ∙ ρ) ⊔ U) hl,?_⟩
    intro v hv
    obtain ⟨a,ha,u,hu,rfl⟩ := Submodule.mem_sup.mp hv
    simp only [LinearMap.map_add₂,hLi hl a ha,hL hl u hu,add_zero]

theorem radical_orthogonal_line_sup_of_nondegenerate (B : LinearMap.BilinForm K V)
    (hB : B.IsAlt) (hND : B.Nondegenerate) (ρ : V) (hρ : ρ ≠ 0)
    (U : Submodule K V) (hU : (B.restrict U).Nondegenerate)
    (hρU : ρ ∈ B.orthogonal U) :
    radical B (B.orthogonal ((K ∙ ρ) ⊔ U)) = K ∙ ρ := by
  rw [radical_orthogonal_eq B hB hND,
    radical_line_sup_of_nondegenerate B hB ρ hρ U hU hρU]

theorem finrank_orthogonal_line_sup_eq (B : LinearMap.BilinForm K V)
    (hB : B.IsAlt) (hND : B.Nondegenerate) (ρ : V) (hρ : ρ ≠ 0)
    (U : Submodule K V) (hU : (B.restrict U).Nondegenerate)
    (hρU : ρ ∈ B.orthogonal U) :
    finrank K (B.orthogonal ((K ∙ ρ) ⊔ U)) =
      finrank K V - (1+finrank K U) := by
  have hL : (K ∙ ρ) ≤ B.orthogonal U :=
    (Submodule.span_singleton_le_iff_mem ρ (B.orthogonal U)).mpr hρU
  have hd : Disjoint (K ∙ ρ) U :=
    ((B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU).disjoint.mono_right hL).symm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ ρ) U
  rw [hd.eq_bot,finrank_bot,add_zero,finrank_span_singleton hρ] at hsum
  rw [B.finrank_orthogonal hND,hsum]

theorem finrank_nine_and_radical_orthogonal_line_sup
    (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (hND : B.Nondegenerate)
    (hV : finrank K V = 14) (ρ : V) (hρ : ρ ≠ 0)
    (U : Submodule K V) (hUd : finrank K U = 4)
    (hU : (B.restrict U).Nondegenerate) (hρU : ρ ∈ B.orthogonal U) :
    finrank K (B.orthogonal ((K ∙ ρ) ⊔ U)) = 9 ∧
      radical B (B.orthogonal ((K ∙ ρ) ⊔ U)) = K ∙ ρ := by
  refine ⟨?_,radical_orthogonal_line_sup_of_nondegenerate B hB hND ρ hρ U hU hρU⟩
  rw [finrank_orthogonal_line_sup_eq B hB hND ρ hρ U hU hρU,hV,hUd]

end M9.RadicalFiber

module

public import M9StacksIntegration.LagrangianChartRegularStalk

/-!
# Fixed-length regular stalk generators under actual open chart maps

These transport lemmas retain the original native stalk ring, the
original stalk-map kernel, and the exact sequence length. The property
abbreviation is the literal existence of a native regular sequence; no
replacement local-ring or codimension certificate is introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingTheory.Sequence

universe u

namespace M9Native.LagrangianDegree

theorem regular_kernel_of_length_ringEquiv
    {R R' S : Type u} [CommRing R] [CommRing R'] [CommRing S]
    (e : R' ≃+* R) (g : R →+* S) (r : ℕ)
    (h : ∃ rs : List R, rs.length = r ∧ IsRegular R rs ∧ Ideal.ofList rs = RingHom.ker g) :
    ∃ rs : List R', rs.length = r ∧ IsRegular R' rs ∧
      Ideal.ofList rs = RingHom.ker (g.comp e.toRingHom) := by
  obtain ⟨rs, hlen, hreg, hker⟩ := h
  refine ⟨rs.map e.symm.toRingHom, by simpa using hlen, ?_, ?_⟩
  · apply (AddEquiv.isRegular_congr (R := R) (S := R')
      (e := e.symm.toAddEquiv) ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun a _ x => e.symm.map_mul a x))
  · rw [← Ideal.map_ofList, hker]
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr ?_) ?_
    · intro y hy
      change g (e (e.symm y)) = 0
      rw [e.apply_symm_apply]
      exact hy
    · intro y hy
      have hy' : e y ∈ RingHom.ker g := hy
      simpa using Ideal.mem_map_of_mem e.symm.toRingHom hy'

abbrev RegularStalkKernel {Z X : Scheme.{u}} (i : Z ⟶ X) (z : Z) (r : ℕ) : Prop :=
  ∃ rs : List (X.presheaf.stalk (i z)), rs.length = r ∧
    IsRegular (X.presheaf.stalk (i z)) rs ∧ Ideal.ofList rs = RingHom.ker (i.stalkMap z).hom

theorem stalkMap_comp_hom {Z W X : Scheme.{u}} (j : Z ⟶ W) (b : W ⟶ X) (z : Z) :
    ((j ≫ b).stalkMap z).hom = (j.stalkMap z).hom.comp (b.stalkMap (j z)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- An actual open immersion on the source changes no stalk kernel. -/
theorem regularStalkKernel_source_open_iff {Z' Z X : Scheme.{u}}
    (a : Z' ⟶ Z) [IsOpenImmersion a] (j : Z ⟶ X) (z : Z') (r : ℕ) :
    RegularStalkKernel (a ≫ j) z r ↔ RegularStalkKernel j (a z) r := by
  have hinj : Function.Injective (a.stalkMap z).hom :=
    (asIso (a.stalkMap z)).commRingCatIsoToRingEquiv.injective
  have hker : RingHom.ker ((a ≫ j).stalkMap z).hom =
      RingHom.ker (j.stalkMap (a z)).hom := by
    rw [stalkMap_comp_hom]
    exact RingHom.ker_comp_of_injective _ hinj
  change (∃ rs : List (X.presheaf.stalk (j (a z))), rs.length = r ∧
      IsRegular (X.presheaf.stalk (j (a z))) rs ∧
        Ideal.ofList rs = RingHom.ker ((a ≫ j).stalkMap z).hom) ↔ _
  rw [hker]

/-- An actual target open chart carries the exact-length regular
generators to the original ambient stalk via its actual stalk iso. -/
theorem regularStalkKernel_target_open {Z W X : Scheme.{u}}
    (j : Z ⟶ W) (b : W ⟶ X) [IsOpenImmersion b] (z : Z) (r : ℕ)
    (h : RegularStalkKernel j z r) : RegularStalkKernel (j ≫ b) z r := by
  have h' := regular_kernel_of_length_ringEquiv
    (asIso (b.stalkMap (j z))).commRingCatIsoToRingEquiv (j.stalkMap z).hom r h
  change ∃ rs : List (X.presheaf.stalk (b (j z))), rs.length = r ∧
    IsRegular (X.presheaf.stalk (b (j z))) rs ∧
      Ideal.ofList rs = RingHom.ker ((j ≫ b).stalkMap z).hom
  rw [stalkMap_comp_hom]
  exact h'

/-- A genuine commuting open-chart square transports the original
fixed-length native regular stalk sequence to the original inclusion. -/
theorem regularStalkKernel_of_open_square {Z' Z W X : Scheme.{u}}
    (a : Z' ⟶ Z) [IsOpenImmersion a] (j : Z ⟶ X)
    (j' : Z' ⟶ W) (b : W ⟶ X) [IsOpenImmersion b]
    (hcart : a ≫ j = j' ≫ b) (z : Z') (r : ℕ)
    (h : RegularStalkKernel j' z r) : RegularStalkKernel j (a z) r := by
  apply (regularStalkKernel_source_open_iff a j z r).mp
  rw [hcart]
  exact regularStalkKernel_target_open j' b z r h

end M9Native.LagrangianDegree

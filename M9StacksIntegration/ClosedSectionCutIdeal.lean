module
public import M9StacksIntegration.IteratedLineSectionCuts
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Actual closed intersections and actual successive section cuts.
The equations identify the original kernel ideal sheaf, including all
nilpotents, by genuine closed-immersion lifts on the original schemes. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory
open Stacks.Divisors
universe u

namespace M9Native.ClosedSectionCutIdeal

/-- The full ideal of an actual closed intersection is the sum of its
original ambient ideals. No equality of supports is used. -/
theorem composite_kernel_of_comap {X Y Z : Scheme.{u}}
    (κ : X ⟶ Y) [IsClosedImmersion κ] (i : Z ⟶ X) [IsClosedImmersion i]
    (J : Y.IdealSheafData) (hi : i.ker = J.comap κ) :
    (i ≫ κ).ker = J ⊔ κ.ker := by
  let S := J ⊔ κ.ker
  have hκS : κ.ker ≤ S.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact le_sup_right
  let u := IsClosedImmersion.lift κ S.subschemeι hκS
  have hu : u ≫ κ = S.subschemeι := IsClosedImmersion.lift_fac κ S.subschemeι hκS
  have hJu : J.comap κ ≤ u.ker := by
    apply (Scheme.IdealSheafData.le_map_iff_comap_le).mp
    rw [Scheme.IdealSheafData.map_ker, hu, Scheme.IdealSheafData.ker_subschemeι]
    exact le_sup_left
  have hiu : i.ker ≤ u.ker := by rw [hi]; exact hJu
  let v := IsClosedImmersion.lift i u hiu
  have hv : v ≫ i = u := IsClosedImmersion.lift_fac i u hiu
  have hcomp : v ≫ (i ≫ κ) = S.subschemeι := by rw [← Category.assoc, hv, hu]
  apply le_antisymm
  · have h := Scheme.Hom.le_ker_comp v (i ≫ κ)
    rw [hcomp, Scheme.IdealSheafData.ker_subschemeι] at h
    exact h
  · apply sup_le
    · rw [Scheme.Hom.ker_comp]
      exact (Scheme.IdealSheafData.le_map_iff_comap_le).mpr hi.ge
    · exact Scheme.Hom.le_ker_comp i κ

variable {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

def equationsIdeal (ss : List Γ(L, ⊤)) : X.IdealSheafData :=
  ⨆ s ∈ ss, zeroScheme X L s

/-- The literal original ideal of the actual simultaneous section cut,
proved using its all-test-scheme universal property. -/
theorem simultaneousCut_kernel (ss : List Γ(L, ⊤)) :
    (IteratedLineSectionCuts.simultaneousCut L ss).hom.ker = equationsIdeal L ss := by
  let C := IteratedLineSectionCuts.simultaneousCut L ss
  let J := equationsIdeal L ss
  have hself : IteratedLineSectionCuts.FactorsThrough C.hom C := ⟨𝟙 _, Category.id_comp _⟩
  have hz := (IteratedLineSectionCuts.simultaneousCut_factors_iff L C.hom ss).mp hself
  have hJ : J ≤ C.hom.ker := by
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    obtain ⟨g, hg⟩ :=
      (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s C.hom).mp (hz s hs)
    have h := Scheme.Hom.le_ker_comp g (zeroScheme X L s).subschemeι
    rw [hg, Scheme.IdealSheafData.ker_subschemeι] at h
    exact h
  have hvan : ∀ s ∈ ss, pullbackGlobalSections J.subschemeι L s = 0 := by
    intro s hs
    have hsJ : zeroScheme X L s ≤ J :=
      le_iSup_of_le s (le_iSup_of_le hs le_rfl)
    exact (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s J.subschemeι).mpr
      ⟨Scheme.IdealSheafData.inclusion hsJ, Scheme.IdealSheafData.inclusion_subschemeι hsJ⟩
  obtain ⟨g,hg⟩ :=
    (IteratedLineSectionCuts.simultaneousCut_factors_iff L J.subschemeι ss).mpr hvan
  apply le_antisymm _ hJ
  have h := Scheme.Hom.le_ker_comp g C.hom
  rw [hg, Scheme.IdealSheafData.ker_subschemeι] at h
  exact h

end M9Native.ClosedSectionCutIdeal

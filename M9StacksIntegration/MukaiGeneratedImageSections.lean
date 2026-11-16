module

public import M9StacksIntegration.MukaiGeneratedImage
public import M9StacksIntegration.MukaiSemiIrreducible
public import M9StacksIntegration.MukaiBundleUniqueness

/-!
# Sections and generation of the actual generated image

These results concern the literal image of Q plus one section. They
preserve the original maps and do not replace the image by its
saturation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive

universe u v

namespace M9Native.MukaiGeneratedImage

section LinearCategory
variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
variable {Q E O I : C} (j : Q ⟶ E) (a : O ⟶ E)

/-- If the ideal acts trivially on the generated quotient, a morphism
from that image to O is zero as soon as maps Q→O vanish and End(O) is
one-dimensional. The ideal inclusion is required to be actually nonzero. -/
theorem hom_unit_eq_zero
    (hQ : ∀ v : Q ⟶ O, v = 0)
    (hO : Module.finrank k (O ⟶ O) = 1)
    (hid : (𝟙 O) ≠ 0)
    (iota : I ⟶ O) (hiota : iota ≠ 0)
    (u : I ⟶ Q) (hrel : iota ≫ a = u ≫ j)
    (v : generatedImage j a ⟶ O) : v = 0 := by
  have hvQ : subobjectMap j a ≫ v = 0 := hQ _
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hO hid (sectionMap j a ≫ v)
  have hrel' : iota ≫ sectionMap j a = u ≫ subobjectMap j a := by
    apply (cancel_mono (inclusion j a)).mp
    simpa only [Category.assoc, sectionMap_inclusion, subobjectMap_inclusion] using hrel
  have hci : c • iota = 0 := by
    calc
      c • iota = iota ≫ (c • 𝟙 O) := by simp only [Linear.comp_smul, Category.comp_id]
      _ = iota ≫ (sectionMap j a ≫ v) := by rw [hc]
      _ = u ≫ (subobjectMap j a ≫ v) := by rw [← Category.assoc, hrel', Category.assoc]
      _ = 0 := by rw [hvQ, comp_zero]
  have hc0 : c = 0 := (smul_eq_zero.mp hci).resolve_right hiota
  have hvO : sectionMap j a ≫ v = 0 := by rw [← hc, hc0, zero_smul]
  apply (cancel_epi (factorThruImage (biprod.desc j a))).mp
  apply biprod.hom_ext'
  · simpa only [subobjectMap, Category.assoc, comp_zero] using hvQ
  · simpa only [sectionMap, Category.assoc, comp_zero] using hvO

end LinearCategory

section Sheaves
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k))
variable (Q E : X.Modules) (j : Q ⟶ E) (a : MukaiBundle.structureModule X ⟶ E)

/-- A generating family of Q together with the one additional section
is a genuine generating family of the actual image. -/
theorem globallyGenerated (hQ : MukaiSemiIrreducible.GloballyGenerated Q) :
    MukaiSemiIrreducible.GloballyGenerated (generatedImage j a) := by
  classical
  obtain ⟨g⟩ := hQ
  let v : SheafOfModules.free (R := X.ringCatSheaf) (g.I ⊕ PUnit.{u+1}) ⟶
      generatedImage j a :=
    Sigma.desc (Sum.elim
      (fun i => SheafOfModules.ιFree i ≫ g.π ≫ subobjectMap j a)
      (fun _ => sectionMap j a))
  have hv : Epi v := by
    rw [epi_iff_cancel_zero]
    intro T b hb
    have hQB : subobjectMap j a ≫ b = 0 := by
      apply (cancel_epi g.π).mp
      apply Sigma.hom_ext
      intro i
      have h := congrArg (fun m => SheafOfModules.ιFree (Sum.inl i) ≫ m) hb
      simpa only [v, SheafOfModules.ιFree, Sigma.ι_comp_desc_assoc,
        Sum.elim_inl, comp_zero, Category.assoc] using h
    have hOB : sectionMap j a ≫ b = 0 := by
      have h := congrArg (fun m => SheafOfModules.ιFree (Sum.inr PUnit.unit) ≫ m) hb
      simpa only [v, SheafOfModules.ιFree, Sigma.ι_comp_desc_assoc,
        Sum.elim_inr, comp_zero, Category.assoc] using h
    apply (cancel_epi (factorThruImage (biprod.desc j a))).mp
    apply biprod.hom_ext'
    · simpa only [subobjectMap, Category.assoc, comp_zero] using hQB
    · simpa only [sectionMap, Category.assoc, comp_zero] using hOB
  exact ⟨⟨g.I ⊕ PUnit.{u+1}, (generatedImage j a).freeHomEquiv v, by
    simpa only [Equiv.symm_apply_apply] using hv⟩⟩

end Sheaves

end M9Native.MukaiGeneratedImage


module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import M9StacksIntegration.AllTestRelocalizeReflection

/-!
# Actual fullness of relocalization for maps preserving ORIGINAL coefficients

Lower-shriek relocalization on unpointed presheaves is not asserted full.
The actual equivalence with presheaves over the represented base instead
proves that precisely the coefficient-preserving maps have a unique actual
preimage. This retains the ORIGINAL structural map to the coefficient base,
as required for genuine curve-family morphisms.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestPointedRelocalizeFull
universe u
variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine relocalization comparison retains the actual structural
map to the represented coefficient base. -/
theorem forgetIso_hom_toYoneda
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    ((smallerBasePresheafForgetIso B S S' hS hS' k).app F).hom ≫
        OverShriek.relocalizeToYoneda k F =
      ((smallerBasePresheafEquivalence B S S' hS hS' k).functor.obj F).hom := by
  ext W s
  apply Over.OverMorphism.ext
  rfl

/-- Every relocalized map preserves its ORIGINAL coefficient structure. -/
theorem map_toYoneda
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : F ⟶ G) :
    (OverShriek.relocalizePresheafFunctor k).map r ≫
        OverShriek.relocalizeToYoneda k G = OverShriek.relocalizeToYoneda k F := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An ACTUAL native map retaining the ORIGINAL coefficient structure
has a unique actual map on the coefficient-base site. The conclusion is
proved from the genuine presheaf/slice equivalence, not assumed fullness. -/
theorem existsUnique_preimage_of_pointed
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : (OverShriek.relocalizePresheafFunctor k).obj F ⟶
      (OverShriek.relocalizePresheafFunctor k).obj G)
    (hf : f ≫ OverShriek.relocalizeToYoneda k G = OverShriek.relocalizeToYoneda k F) :
    ∃! r : F ⟶ G, (OverShriek.relocalizePresheafFunctor k).map r = f := by
  let E := smallerBasePresheafEquivalence B S S' hS hS' k
  let L := OverShriek.relocalizePresheafFunctor k
  let e := smallerBasePresheafForgetIso B S S' hS hS' k
  let f' := (e.app F).hom ≫ f ≫ (e.app G).inv
  have hcG : (e.app G).inv ≫ (E.functor.obj G).hom =
      OverShriek.relocalizeToYoneda k G := by
    rw [← forgetIso_hom_toYoneda B S S' hS hS' k G, Iso.inv_hom_id_assoc]
  have hf' : f' ≫ (E.functor.obj G).hom = (E.functor.obj F).hom := by
    calc
      f' ≫ (E.functor.obj G).hom =
          (e.app F).hom ≫ f ≫ OverShriek.relocalizeToYoneda k G := by
        change ((e.app F).hom ≫ f ≫ (e.app G).inv) ≫ _ = _
        rw [Category.assoc, Category.assoc, hcG]
      _ = (e.app F).hom ≫ OverShriek.relocalizeToYoneda k F := by rw [hf]
      _ = (E.functor.obj F).hom := forgetIso_hom_toYoneda B S S' hS hS' k F
  let fO : E.functor.obj F ⟶ E.functor.obj G := Over.homMk f' hf'
  let r : F ⟶ G := E.functor.preimage fO
  have hrO : E.functor.map r = fO := E.functor.map_preimage fO
  have hn : (E.functor.map r).left ≫ (e.app G).hom = (e.app F).hom ≫ L.map r :=
    e.hom.naturality r
  have hleft : (e.app F).hom ≫ f = (e.app F).hom ≫ L.map r := by
    rw [hrO] at hn
    simpa only [fO, f', Over.homMk_left, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hn
  have hr : L.map r = f := (cancel_epi (e.app F).hom).mp hleft.symm
  refine ⟨r, hr, ?_⟩
  intro r' hr'
  let : L.Faithful := relocalizePresheaf_faithful k
  exact L.map_injective (hr'.trans hr.symm)

end M9StacksIntegration.AllTestPointedRelocalizeFull

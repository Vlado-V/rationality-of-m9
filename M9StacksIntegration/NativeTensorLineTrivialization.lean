module

public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf

/-! Native tensor cancellation by an actual line trivialization is
natural in the other module. No unit-compatibility equation is assumed. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.NativeTensorLineTrivialization

open MukaiBundleDeterminant (tensor tensorIso)

variable {X : Scheme.{u}}

abbrev unit : X.Modules := SheafOfModules.unit X.ringCatSheaf

def tensorRight (L : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf).flip.obj L

def untwistIso (A L : X.Modules) (τ : L ≅ unit) : tensor A L ≅ A :=
  tensorIso (Iso.refl A) τ ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 A

theorem untwistIso_naturality {A B : X.Modules} (f : A ⟶ B) (L : X.Modules) (τ : L ≅ unit) :
    (tensorRight L).map f ≫ (untwistIso B L τ).hom = (untwistIso A L τ).hom ≫ f := by
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf
  have hτ := (T.map f).naturality τ.hom
  have hunit := Stacks.IdealTorsion.Eta.tensorProductRightUnitor_naturality
    X.presheaf X.ringCatSheaf.2 f
  change ((T.map f).app unit ≫ (T.obj B).map (𝟙 unit)) ≫
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 B).hom =
    (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 A).hom ≫ f at hunit
  rw [CategoryTheory.Functor.map_id,Category.comp_id] at hunit
  simp only [untwistIso,Iso.trans_hom,tensorIso,CategoryTheory.Functor.mapIso_refl,
    Iso.app_hom,CategoryTheory.Functor.mapIso_hom,Iso.refl_hom,
    CategoryTheory.Functor.map_id,NatTrans.id_app,Category.id_comp]
  change (T.map f).app L ≫ (T.obj B).map τ.hom ≫
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 B).hom =
    ((T.obj A).map τ.hom ≫
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 A).hom) ≫ f
  rw [← Category.assoc,← hτ,Category.assoc,hunit,Category.assoc]

theorem untwistIso_inv_naturality {A B : X.Modules} (f : A ⟶ B) (L : X.Modules) (τ : L ≅ unit) :
    (untwistIso A L τ).inv ≫ (tensorRight L).map f = f ≫ (untwistIso B L τ).inv := by
  apply (cancel_mono (untwistIso B L τ).hom).mp
  rw [Category.assoc,untwistIso_naturality]
  simp only [Iso.inv_hom_id_assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- A perfect actual negative/positive pairing and an actual positive-line
trivialization produce the actual negative-line trivialization. -/
def cancellationIso (N L : X.Modules) (e : tensor N L ≅ unit) (τ : L ≅ unit) : N ≅ unit :=
  (untwistIso N L τ).symm ≪≫ e

theorem cancellation_factor {A N : X.Modules} (f : A ⟶ N) (L : X.Modules)
    (e : tensor N L ≅ unit) (τ : L ≅ unit) :
    (untwistIso A L τ).inv ≫ (tensorRight L).map f ≫ e.hom =
      f ≫ (cancellationIso N L e τ).hom := by
  rw [← Category.assoc,untwistIso_inv_naturality]
  rfl

end M9Native.NativeTensorLineTrivialization

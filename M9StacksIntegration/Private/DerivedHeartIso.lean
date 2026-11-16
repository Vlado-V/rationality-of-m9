module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing

/-!
# Homology-normalized comparisons with a sheaf in degree zero

The actual degree-zero homology functor is fully faithful between derived
objects concentrated in degree zero. Lifting its maps therefore constructs
isomorphisms, with their normalization and naturality recorded explicitly.
This is a helper for the original smooth naive cotangent complex.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace M9Native.DerivedHeartIso

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

abbrev H0 : DerivedCategory C ⥤ C := DerivedCategory.homologyFunctor C 0

def lift (A B : DerivedCategory C) [A.IsLE 0] [B.IsGE 0]
    (f : (H0 (C := C)).obj A ⟶ (H0 (C := C)).obj B) : A ⟶ B :=
  (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE A B 0).surjective f |>.choose

@[simp] theorem H0_map_lift (A B : DerivedCategory C) [A.IsLE 0] [B.IsGE 0]
    (f : (H0 (C := C)).obj A ⟶ (H0 (C := C)).obj B) :
    (H0 (C := C)).map (lift A B f) = f :=
  (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE A B 0).surjective f |>.choose_spec

def iso (A B : DerivedCategory C) [A.IsLE 0] [A.IsGE 0] [B.IsLE 0] [B.IsGE 0]
    (e : (H0 (C := C)).obj A ≅ (H0 (C := C)).obj B) : A ≅ B where
  hom := lift A B e.hom
  inv := lift B A e.inv
  hom_inv_id := by
    apply (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE A A 0).injective
    simp only [Functor.map_comp, H0_map_lift, Iso.hom_inv_id]
    exact ((DerivedCategory.homologyFunctor C 0).map_id A).symm
  inv_hom_id := by
    apply (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE B B 0).injective
    simp only [Functor.map_comp, H0_map_lift, Iso.inv_hom_id]
    exact ((DerivedCategory.homologyFunctor C 0).map_id B).symm

@[simp] theorem H0_map_iso_hom (A B : DerivedCategory C)
    [A.IsLE 0] [A.IsGE 0] [B.IsLE 0] [B.IsGE 0]
    (e : (H0 (C := C)).obj A ≅ (H0 (C := C)).obj B) :
    (H0 (C := C)).map (iso A B e).hom = e.hom := H0_map_lift A B e.hom

def toSingle (A : DerivedCategory C) [A.IsLE 0] [A.IsGE 0] (M : C)
    (e : (H0 (C := C)).obj A ≅ M) :
    A ≅ (DerivedCategory.singleFunctor C 0).obj M :=
  iso A _ (e ≪≫ ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).symm)

theorem H0_map_toSingle_hom (A : DerivedCategory C) [A.IsLE 0] [A.IsGE 0] (M : C)
    (e : (H0 (C := C)).obj A ≅ M) :
    (H0 (C := C)).map (toSingle A M e).hom ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).hom = e.hom := by
  simp only [toSingle, H0_map_iso_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem toSingle_naturality (A B : DerivedCategory C)
    [A.IsLE 0] [A.IsGE 0] [B.IsLE 0] [B.IsGE 0] (M N : C)
    (eA : (H0 (C := C)).obj A ≅ M) (eB : (H0 (C := C)).obj B ≅ N)
    (f : A ⟶ B) (g : M ⟶ N)
    (h : (H0 (C := C)).map f ≫ eB.hom = eA.hom ≫ g) :
    f ≫ (toSingle B N eB).hom =
      (toSingle A M eA).hom ≫ (DerivedCategory.singleFunctor C 0).map g := by
  apply (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    A ((DerivedCategory.singleFunctor C 0).obj N) 0).injective
  apply (cancel_mono ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app N).hom).1
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality g
  change (H0 (C := C)).map ((DerivedCategory.singleFunctor C 0).map g) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app N).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).hom ≫ g at hn
  simp only [Functor.map_comp, Category.assoc, H0_map_toSingle_hom, hn]
  rw [← Category.assoc, H0_map_toSingle_hom]
  exact h

end M9Native.DerivedHeartIso

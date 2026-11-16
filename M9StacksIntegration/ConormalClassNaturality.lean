module

public import M9StacksIntegration.ConormalClassComponents

/-!
# Naturality of the original conormal cochain representative

All signs and single-complex identifications are those of the original
native representative. The compatible-morphism application will supply
the actual degree-minus-one conormal map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

universe u v u' v'

namespace M9Native.ConormalClassNaturality

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B A' B' G : C} (d : A ⟶ B) (e : A' ⟶ B')
  (a : double d ComplexShape.upIntRelNegOneZero ⟶
    double e ComplexShape.upIntRelNegOneZero) (δ : A' ⟶ G)

/-- An arbitrary actual chain map pulls the original conormal cochain
back by its actual degree-minus-one component. -/
theorem classMap_naturality :
    a ≫ ConormalClassCochain.classMap e δ =
      ConormalClassCochain.classMap d
        ((doubleXIso₀ d ComplexShape.upIntRelNegOneZero).inv ≫
          a.f (-1) ≫ (doubleXIso₀ e ComplexShape.upIntRelNegOneZero).hom ≫ δ) := by
  apply HomologicalComplex.from_double_hom_ext
  · apply (cancel_mono (ConormalClassComponents.coefficientIso G).hom).mp
    simp only [HomologicalComplex.comp_f, Category.assoc,
      ConormalClassComponents.classMap_f_negOne,
      Preadditive.comp_neg, Iso.hom_inv_id_assoc]
  · simp only [HomologicalComplex.comp_f,
      ConormalClassComponents.classMap_f_zero, comp_zero]

/-- Coefficient transport of the literal representative is ordinary
postcomposition of the original conormal homomorphism. -/
theorem classMap_coefficient {H : C} (δ₀ : A ⟶ G) (c : G ⟶ H) :
    ConormalClassCochain.classMap d δ₀ ≫
      ((CochainComplex.singleFunctor C 0).map c)⟦(1 : ℤ)⟧' =
      ConormalClassCochain.classMap d (δ₀ ≫ c) := by
  simp only [ConormalClassCochain.classMap, Functor.map_comp, Category.assoc]

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- The actual original coefficient identification after mapping a
shifted single complex termwise. -/
theorem coefficientIso_map (H : C) :
    ((((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
        ((CochainComplex.singleFunctor C 0).obj H)).f (-1)) ≫
      (((singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app H)⟦(1 : ℤ)⟧').f (-1) ≫
      (ConormalClassComponents.coefficientIso (F.obj H)).hom =
      F.map (ConormalClassComponents.coefficientIso H).hom := by
  simp [ConormalClassComponents.coefficientIso,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso,
    singleMapHomologicalComplex_hom_app_self]

/-- Mapping the original representative termwise gives the original
representative of the mapped conormal homomorphism, with the genuine
shift and single-complex comparisons. -/
theorem classMap_map {H : C} (δ₀ : A ⟶ H) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ConormalClassCochain.classMap d δ₀) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
        ((CochainComplex.singleFunctor C 0).obj H) ≫
      ((singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app H)⟦(1 : ℤ)⟧' =
    (doubleMapFunctorIso F d ComplexShape.upIntRelNegOneZero (by decide)).inv ≫
      ConormalClassCochain.classMap (F.map d) (F.map δ₀) := by
  apply (cancel_epi (doubleMapFunctorIso F d
    ComplexShape.upIntRelNegOneZero (by decide)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply HomologicalComplex.from_double_hom_ext
  · apply (cancel_mono (ConormalClassComponents.coefficientIso (F.obj H)).hom).mp
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      doubleMapFunctorIso, asIso_hom, doubleMapFunctorHom, mkHomFromDouble_f₀,
      Category.assoc, coefficientIso_map,
      ← Functor.map_comp, ConormalClassComponents.classMap_f_negOne,
      Functor.map_neg, Preadditive.comp_neg, Iso.inv_hom_id_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (F.obj H) 1 (by decide)).eq_of_tgt _ _

end M9Native.ConormalClassNaturality

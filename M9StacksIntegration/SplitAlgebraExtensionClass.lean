module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChange

/-! Vanishing of the actual class of an algebra extension with a genuine
algebra section, using its canonical lifted presentation. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Sites.FreeAlgebra
open Stacks.Sites.Conormal

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.SplitAlgebraExtensionClass

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : AlgebraSquareZeroExtension f G) (σ : X.sheaf ⟶ P.sheaf)
  (hσ : σ ≫ P.reduction = 𝟙 _) (hb : structureRingMap f ≫ σ = P.base)

def generators : underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf ⟶
    underlyingPresheaf (Opens.grothendieckTopology X.carrier) P.sheaf :=
  Functor.whiskerRight σ.hom (forget CommRingCat.{u})

include hσ in
theorem generators_comp : generators P σ ≫ P.generatorsMap = 𝟙 _ := by
  change Functor.whiskerRight σ.hom (forget CommRingCat.{u}) ≫
    Functor.whiskerRight P.reduction.hom (forget CommRingCat.{u}) = 𝟙 _
  rw [← Functor.whiskerRight_comp]
  have h := congrArg (fun q => q.hom) hσ
  change σ.hom ≫ P.reduction.hom = 𝟙 _ at h
  exact (congrArg (fun q => Functor.whiskerRight q (forget CommRingCat.{u})) h).trans
    (Functor.whiskerRight_id' _)

def presentation : PresentedSquareZeroExtension f G
    (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (𝟙 _) :=
  P.presentedBy (generators P σ) (generators_comp P σ hσ)

local instance canonicalPresentationSurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f (underlyingPresheaf
        (Opens.grothendieckTopology X.carrier) X.sheaf) (𝟙 _)).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

include hb in
theorem lift_presentation : (presentation P σ hσ).lift =
    generatorsPresentation f _ (𝟙 _) ≫ σ := by
  apply freeAlgebraSheaf_hom_ext
  · rw [freeAlgebraSheafCoefficientMap_comp_desc, ← Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc]
    exact hb.symm
  · have hw : Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
          (generatorsPresentation f _ (𝟙 _) ≫ σ)) (forget CommRingCat.{u}) =
      Functor.whiskerRight
        ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
          (generatorsPresentation f _ (𝟙 _))) (forget CommRingCat.{u}) ≫
        Functor.whiskerRight σ.hom (forget CommRingCat.{u}) :=
      (congrArg (Functor.whiskerRight · (forget CommRingCat.{u}))
        (Functor.map_comp _ _ _)).trans (Functor.whiskerRight_comp _ _ _)
    rw [freeAlgebraSheafVariable_comp_desc, hw, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc, Category.id_comp]
    rfl

include hb in
theorem conormalToIdeal_presentation : (presentation P σ hσ).conormalToIdeal = 0 := by
  apply conormal_hom_ext
  intro U x
  rw [conormalDesc_toAssociatedModule, PresentedSquareZeroExtension.idealRestriction_app]
  have hz : (((presentation P σ hσ).lift).hom.app U).hom x.1 = 0 := by
    rw [lift_presentation P σ hσ hb]
    change (σ.hom.app U).hom
      (((generatorsPresentation f _ (𝟙 _)).hom.app U).hom x.1) = 0
    rw [x.2, map_zero]
  have he : (⟨(((presentation P σ hσ).lift).hom.app U).hom x.1,
      (presentation P σ hσ).lift_mem_kernelIdeal U x⟩ :
        kernelIdeal P.reduction.hom U) = 0 := Subtype.ext hz
  change P.ideal.app U _ = 0
  rw [he, map_zero]

include hσ hb in
theorem extClass_eq_zero_of_algebra_section : P.toPresented.extClass = 0 := by
  rw [← P.presentedBy_extClass (generators P σ) (generators_comp P σ hσ)]
  change (presentation P σ hσ).extClass = 0
  simp only [PresentedSquareZeroExtension.extClass,
    PresentedSquareZeroExtension.presentedExtClass,
    conormalToIdeal_presentation P σ hσ hb,
    NaiveCotangentTwoTerm.conormalExtClass, Functor.map_zero, comp_zero]

end M9Native.SplitAlgebraExtensionClass

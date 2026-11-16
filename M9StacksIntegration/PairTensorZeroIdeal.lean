module

public import M9StacksIntegration.PairTensorUnitMorphism

/-! Actual split image lines identify the FULL incidence zero ideal
with the FULL raw hyperplane zero ideal. Universal monicity is proved
from the actual retraction and vanishing is tested on every scheme. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.PairTensorZeroIdeal
open LagrangianMatrixChart LinearIncidenceTensorCoordinates TensorUnitSections

variable {X P : Scheme.{u}} (p : P ⟶ X) (F : X.Modules) (L : P.Modules)
  (τ : (Scheme.Modules.pullback p).obj (freeOn X 2) ⟶ L)
  (j : Scheme.unitModule X ⟶ F) (r : F ⟶ Scheme.unitModule X)
  (hret : j ≫ r = 𝟙 (Scheme.unitModule X))

def columnRetraction : (Scheme.Modules.pullback p).obj F ⟶ Scheme.unitModule P :=
  (Scheme.Modules.pullback p).map r ≫ (Scheme.Modules.pullbackUnitIso p).hom

include hret in
theorem column_retraction : PairTensorUnitMorphism.column p F j ≫ columnRetraction p F r = 𝟙 _ := by
  rw [PairTensorUnitMorphism.column,columnRetraction,Category.assoc,
    ← Functor.map_comp_assoc,hret,CategoryTheory.Functor.map_id,Category.id_comp,Iso.inv_hom_id]

def imageRetraction : tensorObj P ((Scheme.Modules.pullback p).obj F) L ⟶ L :=
  tensorFirst (columnRetraction p F r) L ≫ (unitTensorIso P L).hom

include hret in
theorem image_retraction : PairTensorUnitMorphism.imageMap p F L j ≫
    imageRetraction p F L r = 𝟙 L := by
  rw [PairTensorUnitMorphism.imageMap,imageRetraction,Category.assoc,tensorFirst,tensorFirst,
    ← Functor.map_comp_assoc,column_retraction p F j r hret,
    CategoryTheory.Functor.map_id,Category.id_comp,Iso.inv_hom_id]

include r hret in
theorem imageMap_universallyMono {T : Scheme.{u}} (f : T ⟶ P) :
    Mono ((Scheme.Modules.pullback f).map (PairTensorUnitMorphism.imageMap p F L j)) := by
  have h : (Scheme.Modules.pullback f).map (PairTensorUnitMorphism.imageMap p F L j) ≫
      (Scheme.Modules.pullback f).map (imageRetraction p F L r) = 𝟙 _ := by
    rw [← Functor.map_comp,image_retraction p F L j r hret,CategoryTheory.Functor.map_id]
  letI : IsSplitMono ((Scheme.Modules.pullback f).map (PairTensorUnitMorphism.imageMap p F L j)) :=
    ⟨⟨(Scheme.Modules.pullback f).map (imageRetraction p F L r),h⟩⟩
  infer_instance

variable (t : Scheme.unitModule X ⟶ Scheme.unitModule X) (i : Fin 2)

def hyperplaneSection : Γ(L,⊤) :=
  τ.app ⊤ (pullbackGlobalSections p (freeOn X 2)
    ((FreeTwoSplitHyperplane.subline X t i).app ⊤ (1 : Γ(X,⊤))))

theorem hyperplaneSection_unitHom :
    Scheme.Modules.unitHomEquivTop L (hyperplaneSection p L τ t i) =
      PairTensorUnitMorphism.hyperplaneMap p L τ t i := by
  have hs : Scheme.Modules.unitHomEquivTop (freeOn X 2)
      ((FreeTwoSplitHyperplane.subline X t i).app ⊤ (1 : Γ(X,⊤))) =
        FreeTwoSplitHyperplane.subline X t i := by
    apply LagrangianSectionGeneration.unitHom_ext_top_one
    exact LagrangianAffineDeterminant.unitHom_top_one _ _
  exact (QuotientSectionMorphism.unitHom_quotient p (freeOn X 2) L τ _).trans
    (congrArg (fun a => (Scheme.Modules.pullbackUnitIso p).inv ≫
      (Scheme.Modules.pullback p).map a ≫ τ) hs)

def vectorIdeal : P.IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal P
    (tensorObj P ((Scheme.Modules.pullback p).obj F) L)
    (PairTensorUnitMorphism.equation p F L τ j t i)

def hyperplaneIdeal : P.IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal P L (hyperplaneSection p L τ t i)

variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1]

include r hret in
/-- Equality of FULL ideals follows from actual morphisms on ALL test
schemes, including nonreduced tests; no radical operation is used. -/
theorem vectorIdeal_eq_hyperplaneIdeal : vectorIdeal p F L τ j t i = hyperplaneIdeal p L τ t i := by
  letI := isFiniteLocallyFreeOfRank_pullback p F 2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (tensorObj P ((Scheme.Modules.pullback p).obj F) L) 2 := by
    exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf
      P ((Scheme.Modules.pullback p).obj F) L 2 1
  apply SectionZeroSubbundle.ideal_eq_of_all_factors
  intro T f
  change (∃ a : T ⟶ (SectionZeroIdealFactorization.sectionZeroIdeal P _
      (PairTensorUnitMorphism.equation p F L τ j t i)).subscheme,
      a ≫ (SectionZeroIdealFactorization.sectionZeroIdeal P _
        (PairTensorUnitMorphism.equation p F L τ j t i)).subschemeι=f) ↔ _
  rw [← SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
      (tensorObj P ((Scheme.Modules.pullback p).obj F) L) 2 _ f]
  change _ ↔ ∃ a : T ⟶ (SectionZeroIdealFactorization.sectionZeroIdeal P L
      (hyperplaneSection p L τ t i)).subscheme,
      a ≫ (SectionZeroIdealFactorization.sectionZeroIdeal P L
        (hyperplaneSection p L τ t i)).subschemeι=f
  rw [← SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough L 1 _ f,
    SplitLineProjectiveZero.pullback_section_eq_zero_iff,
    SplitLineProjectiveZero.pullback_section_eq_zero_iff]
  have he := PairTensorUnitMorphism.equation_unitHom p F L τ j t i
  rw [← hyperplaneSection_unitHom p L τ t i] at he
  rw [he,Functor.map_comp]
  letI := imageMap_universallyMono p F L j r hret f
  constructor
  · intro h
    exact (cancel_mono ((Scheme.Modules.pullback f).map
      (PairTensorUnitMorphism.imageMap p F L j))).mp (by simpa using h)
  · intro h
    rw [h,zero_comp]

end M9Native.PairTensorZeroIdeal

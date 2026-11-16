module

public import M9StacksIntegration.FreeTwoProjectiveChartCoordinates
public import M9StacksIntegration.LagrangianSectionGeneration

/-! Section transport is first proved as an identity of actual module
morphisms. This avoids expanding the relative-Proj global-section
dictionary before applying the genuine unit-Hom comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.Scheme.unitModule
  SheafOfModules.unit PresheafOfModules.unit

namespace M9Native.QuotientSectionMorphism

theorem unitHom_quotient {A P : Scheme.{u}} (p : P ⟶ A)
    (E : A.Modules) (L : P.Modules) (v : (Scheme.Modules.pullback p).obj E ⟶ L)
    (s : Γ(E,⊤)) :
    Scheme.Modules.unitHomEquivTop L
      (v.app ⊤ (pullbackGlobalSections p E s)) =
      (Scheme.Modules.pullbackUnitIso p).inv ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.unitHomEquivTop E s) ≫ v := by
  apply LagrangianSectionGeneration.unitHom_ext_top_one
  refine (LagrangianAffineDeterminant.unitHom_top_one L _).trans ?_
  symm
  change v.app ⊤ (((Scheme.Modules.pullback p).map
    (Scheme.Modules.unitHomEquivTop E s)).app ⊤
      ((Scheme.Modules.pullbackUnitIso p).inv.app ⊤ (1 : Γ(P,⊤)))) = _
  rw [FreeTwoProjectiveChartCoordinates.inverse_pullbackUnitIso_one,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]
  exact congrArg (fun z => v.app ⊤ (pullbackGlobalSections p E z))
    (LagrangianAffineDeterminant.unitHom_top_one E s)

theorem inverse_unit_composite {A P T : Scheme.{u}} (p : P ⟶ A)
    (f : T ⟶ P) (g : T ⟶ A) (hg : f ≫ p=g) :
    (Scheme.Modules.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullbackCongr hg).inv.app (Scheme.unitModule A) ≫
        (Scheme.Modules.pullbackComp f p).inv.app (Scheme.unitModule A) =
      (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso p).inv := by
  apply (cancel_mono ((Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso p).hom ≫
    (Scheme.Modules.pullbackUnitIso f).hom)).mp
  calc
    _ = (Scheme.Modules.pullbackUnitIso g).inv ≫
        ((Scheme.Modules.pullbackCongr hg).inv.app (Scheme.unitModule A) ≫
          (Scheme.Modules.pullbackComp f p).inv.app (Scheme.unitModule A) ≫
          (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso p).hom ≫
          (Scheme.Modules.pullbackUnitIso f).hom) := by simp only [Category.assoc]
    _ = 𝟙 _ := by
      rw [Scheme.Modules.pullbackUnitIso_comp_eq f p g hg,Iso.inv_hom_id]
    _ = _ := by
      simp only [Category.assoc,← Functor.map_comp_assoc,Iso.inv_hom_id]
      rw [CategoryTheory.Functor.map_id,Category.id_comp,Iso.inv_hom_id]

/-- The original quotient and the induced quotient give the same
actual unit-to-line morphism under the actual pullback comparison. -/
theorem quotient_unit_morphism_transport {A P T : Scheme.{u}} (p : P ⟶ A)
    (E : A.Modules) (L : P.Modules) (v : (Scheme.Modules.pullback p).obj E ⟶ L)
    (σ : Scheme.unitModule A ⟶ E) (f : T ⟶ P) (g : T ⟶ A) (hg : f ≫ p=g) :
    (Scheme.Modules.pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map σ ≫
        (Scheme.Modules.pullbackCongr hg).inv.app E ≫
        (Scheme.Modules.pullbackComp f p).inv.app E ≫ (Scheme.Modules.pullback f).map v =
      (Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map σ ≫ v) := by
  have hc := (Scheme.Modules.pullbackCongr hg).inv.naturality σ
  have hp := (Scheme.Modules.pullbackComp f p).inv.naturality σ
  change (Scheme.Modules.pullback g).map σ ≫
      (Scheme.Modules.pullbackCongr hg).inv.app E =
    (Scheme.Modules.pullbackCongr hg).inv.app (Scheme.unitModule A) ≫
      (Scheme.Modules.pullback (f ≫ p)).map σ at hc
  change (Scheme.Modules.pullback (f ≫ p)).map σ ≫
      (Scheme.Modules.pullbackComp f p).inv.app E =
    (Scheme.Modules.pullbackComp f p).inv.app (Scheme.unitModule A) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback p).map σ) at hp
  rw [reassoc_of% hc,reassoc_of% hp]
  rw [reassoc_of% (inverse_unit_composite p f g hg)]
  simp only [Functor.map_comp]

end M9Native.QuotientSectionMorphism

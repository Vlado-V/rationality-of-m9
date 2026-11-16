module

public import M9StacksIntegration.DirectImageTwoTermKernel
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Actual arbitrary pullback of the actual two-term differential

Naturality of the canonical flat-single comparison fixes the pulled
bundle morphism. Hence the resulting kernel is the kernel of the actual
ordinary pullback of the original global differential.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction DerivedCategory

universe u

namespace M9Native.DirectImageTwoTermPullback

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (derivedToOrdinaryPullbackSingle)

private theorem single_map_native_eq {S : Scheme.{u}} {M N : S.Modules} (d : M ⟶ N) :
    (singleFunctor (SheafOfModules.{u} (structureSheafRing S.toSheafedSpace)) 0).map d =
      (singleFunctor S.Modules 0).map d := by
  rfl


/-- Naturality of the genuine canonical derived-to-ordinary single comparison. -/
theorem derivedToOrdinarySingle_naturality {X Y : RingedSpace.{u,u}} (f : X ⟶ Y)
    {M M' : SheafOfModules.{u} (structureSheafRing Y)} (g : M ⟶ M') (d : ℤ) :
    (derivedPullback f).map ((singleFunctor _ d).map g) ≫ derivedToOrdinaryPullbackSingle f M' d =
      derivedToOrdinaryPullbackSingle f M d ≫
        (singleFunctor _ d).map ((modulePullback f).map g) := by
  have h1 := (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).hom.naturality g
  have h2 := (derivedPullbackComparison f).naturality
    ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map g)
  have h3 := ((modulePullback f).mapHomotopyCategorySingleFunctor d).hom.naturality g
  have h4 := (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d).inv.naturality
    ((modulePullback f).map g)
  simp only [Functor.comp_map] at h1 h2 h3 h4
  simp only [derivedToOrdinaryPullbackSingle,Category.assoc]
  rw [← Functor.map_comp_assoc,h1,Functor.map_comp_assoc,reassoc_of% h2,
    ← Functor.map_comp_assoc Qh,h3,Functor.map_comp_assoc,h4]

/-- Actual derived pullback transports a genuine bundle two-term triangle
with precisely the ordinary pulled-back bundle differential. -/
theorem pullback_twoTermTriangle
    {Y S : Scheme.{u}} (g : Y ⟶ S) {K : DerivedCategory S.Modules}
    {E F : S.Modules} (rE rF : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E rE)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF)
    (a : K ⟶ (singleFunctor S.Modules 0).obj E) (d : E ⟶ F)
    (b : (singleFunctor S.Modules 0).obj F ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a ((singleFunctor S.Modules 0).map d) b ∈
      distTriang (DerivedCategory S.Modules)) :
    ∃ (a' : (derivedPullback g.toLRSHom.toShHom).obj K ⟶
        (singleFunctor Y.Modules 0).obj ((Scheme.Modules.pullback g).obj E))
      (b' : (singleFunctor Y.Modules 0).obj ((Scheme.Modules.pullback g).obj F) ⟶
        ((derivedPullback g.toLRSHom.toShHom).obj K)⟦(1 : ℤ)⟧),
      Triangle.mk a' ((singleFunctor Y.Modules 0).map ((Scheme.Modules.pullback g).map d)) b' ∈
        distTriang (DerivedCategory Y.Modules) := by
  let R := derivedPullback g.toLRSHom.toShHom
  let T := R.mapTriangle.obj (Triangle.mk a ((singleFunctor S.Modules 0).map d) b)
  let eE := PoincareChern.OrdinaryDegreeZero.flatSinglePullbackIso g.toLRSHom.toShHom E
    (SheafOfModules.isFlat_of_isFiniteLocallyFree E hE.isFiniteLocallyFree) 0 ≪≫
      (singleFunctor Y.Modules 0).mapIso ((Stacks.ProjectiveBundleQuotients.pullbackIso g).symm.app E)
  let eF := PoincareChern.OrdinaryDegreeZero.flatSinglePullbackIso g.toLRSHom.toShHom F
    (SheafOfModules.isFlat_of_isFiniteLocallyFree F hF.isFiniteLocallyFree) 0 ≪≫
      (singleFunctor Y.Modules 0).mapIso ((Stacks.ProjectiveBundleQuotients.pullbackIso g).symm.app F)
  let a' := T.mor₁ ≫ eE.hom
  let b' := eF.inv ≫ T.mor₃
  refine ⟨a',b',?_⟩
  have hT' : T ∈ distTriang (DerivedCategory Y.Modules) := R.map_distinguished _ hT
  apply isomorphic_distinguished T hT' _
  refine Triangle.isoMk _ _ (Iso.refl _) eE.symm eF.symm ?_ ?_ ?_
  · simp [a',Category.assoc]
  · apply (cancel_mono eF.hom).1
    apply (cancel_epi eE.hom).1
    have hn := derivedToOrdinarySingle_naturality g.toLRSHom.toShHom d 0
    have hp := (Stacks.ProjectiveBundleQuotients.pullbackIso g).inv.naturality d
    have hc : R.map ((singleFunctor S.Modules 0).map d) ≫ eF.hom =
        eE.hom ≫ (singleFunctor Y.Modules 0).map ((Scheme.Modules.pullback g).map d) := by
      let J := singleFunctor (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)) 0
      have h1 := congrArg (fun z => z ≫ J.map ((Stacks.ProjectiveBundleQuotients.pullbackIso g).inv.app F)) hn
      have h2 := congrArg (fun z => J.map z) hp
      have h3 := congrArg (fun z => derivedToOrdinaryPullbackSingle g.toLRSHom.toShHom E 0 ≫ z) h2
      simp only [Functor.map_comp,Category.assoc] at h1 h3
      simpa only [eE,eF,R,J,Iso.trans_hom,Functor.mapIso_hom,
        PoincareChern.OrdinaryDegreeZero.flatSinglePullbackIso,asIso_hom,
        Iso.app_hom,Iso.symm_hom,Category.assoc,
        single_map_native_eq (S := S),single_map_native_eq (S := Y)] using h1.trans h3
    simpa [T,Category.assoc] using hc.symm
  · simp [b',Category.assoc]

/-- The genuine kernel comparison after every actual scheme base change. -/
theorem nonempty_pullback_homologyZeroIsoKernel
    {Y S : Scheme.{u}} (g : Y ⟶ S) {K : DerivedCategory S.Modules}
    {E F : S.Modules} (rE rF : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E rE)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF)
    (a : K ⟶ (singleFunctor S.Modules 0).obj E) (d : E ⟶ F)
    (b : (singleFunctor S.Modules 0).obj F ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a ((singleFunctor S.Modules 0).map d) b ∈
      distTriang (DerivedCategory S.Modules)) :
    Nonempty ((homologyFunctor Y.Modules 0).obj
      ((derivedPullback g.toLRSHom.toShHom).obj K) ≅
        kernel ((Scheme.Modules.pullback g).map d)) := by
  obtain ⟨a',b',hT'⟩ := pullback_twoTermTriangle g rE rF hE hF a d b hT
  exact DirectImageTwoTermKernel.nonempty_homologyZeroIsoKernel a' _ b' hT'

end M9Native.DirectImageTwoTermPullback

module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.Assembly
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree

/-!
# Ordinary degree-zero direct image from the genuine derived direct image

This uses only already checked generic proper-flat and derived functor
providers. It does not import Picard representability, the field-spectrum
cohomology comparison, the affine Cech degeneration or the broader
single-degree pullback locus provider. The isomorphisms are actual
ordinary module sheaf isomorphisms.

The chosen-resolution argument is the generic part of the pinned native
ProperFlatDegreeZeroDirectImage provider, and the flat-single comparison
is the generic part of SingleDegreeRankOpenDerivedPullback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace M9Native.PoincareChern.OrdinaryDegreeZero

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
  _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

open ProperFlatFibreEulerCharacteristic

def derivedPushforwardModuleIsoInjectiveResolution {Y T : Scheme.{u}} (g : Y ⟶ T)
    (F : Y.Modules) :
    derivedPushforwardModule g F ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((modulePushforward g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)).obj
          (injectiveResolution F).cochainComplex)) :=
  have hQ : IsIso (DerivedCategory.Q.map (injectiveResolution F).ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hK : (injectiveResolution F).cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective _ 0
  have : IsIso ((derivedPushforwardUnit g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (injectiveResolution F).cochainComplex)) :=
    isIso_derivedPushforwardUnit_app_of_isKInjective g.toLRSHom.toShHom _ hK
  (derivedPushforward g.toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map (injectiveResolution F).ι') hQ ≪≫
        (DerivedCategory.quotientCompQhIso _).symm.app _) ≪≫
    (asIso ((derivedPushforwardUnit g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (injectiveResolution F).cochainComplex))).symm

def hdiIsoHomologyDerivedPushforwardModule {Y T : Scheme.{u}} (g : Y ⟶ T) (F : Y.Modules)
    (q : ℕ) :
    Stacks.AlgebraicGeometry.LerayAffineBase.hdi g q F ≅
      (DerivedCategory.homologyFunctor T.Modules q).obj (derivedPushforwardModule g F) :=
  (Stacks.DerivedIndexing.rightDerivedIsoRes (Scheme.Modules.pushforward g) q).app F ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ (q : ℤ)).app _ ≪≫
    ((DerivedCategory.homologyFunctor T.Modules (q : ℤ)).mapIso
      (derivedPushforwardModuleIsoInjectiveResolution g F) ≪≫
    (DerivedCategory.homologyFunctorFactorsh T.Modules (q : ℤ)).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ (q : ℤ)).app _).symm

/-- Degree zero is the actual ordinary pushforward. -/
def pushforwardIsoOfIsoSingle {Y T : Scheme.{u}} {g : Y ⟶ T} {F : Y.Modules} {P : T.Modules}
    (e : derivedPushforwardModule g F ≅ (DerivedCategory.singleFunctor T.Modules 0).obj P) :
    (Scheme.Modules.pushforward g).obj F ≅ P :=
  have := Stacks.SchemeCohomology.pushforward_preservesFiniteLimits g
  ((Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.app F).symm ≪≫
    hdiIsoHomologyDerivedPushforwardModule g F 0 ≪≫
    (DerivedCategory.homologyFunctor T.Modules 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso T.Modules 0).app P

/-- The actual ordinary bundle has the genuine derived rank. -/
theorem ordinaryPushforward_rank_of_derivedRank
    {Y T : Scheme.{u}} (g : Y ⟶ T) (F : Y.Modules) (r : ℕ)
    (hr : HasDerivedPushforwardRank g F 0 r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pushforward g).obj F) r := by
  obtain ⟨E,hE,⟨e⟩⟩ := hr
  exact Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso
    (pushforwardIsoOfIsoSingle e).symm hE

/-- This is the actual canonical comparison at a flat sheaf, in every degree. -/
def flatSinglePullbackIso {X Y : RingedSpace.{u,u}} (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y))
    (hM : SheafOfModules.IsFlat.{u,u,u,u} (O := Y.sheaf) M) (d : ℤ) :
    (derivedPullback f).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M) ≅
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
      ((modulePullback f).obj M) := by
  have h : IsIso (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle f M d) :=
    by
      have hK : IsIso ((derivedPullbackComparison f).app
          ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M)) :=
        Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
          (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf M hM d)
      unfold Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle
      infer_instance
  exact @asIso _ _ _ _ _ h

/-- Actual arbitrary cartesian base change of the actual ordinary
pushforward bundle of an actual invertible family. -/
def ordinaryPushforwardPullbackIso
    {Y T T' Y' : Scheme.{u}} (g : Y ⟶ T) (hfp : FinitePresentation g)
    [IsProper g] [Flat g] (L : Y.Modules) [hL : Stacks.Ample.IsInvertibleModule Y L]
    (r : ℕ) (hr : HasDerivedPushforwardRank g L 0 r)
    (a : T' ⟶ T) (g' : Y' ⟶ T') (q : Y' ⟶ Y) (hsq : IsPullback q g' g a) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pushforward g).obj L) ≅
      (Scheme.Modules.pushforward g').obj ((Scheme.Modules.pullback q).obj L) := by
  let E := hr.choose
  have hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r := hr.choose_spec.1
  let e : derivedPushforwardModule g L ≅ (DerivedCategory.singleFunctor T.Modules 0).obj E :=
    hr.choose_spec.2.some
  let E₀ := (Scheme.Modules.pushforward g).obj L
  let e₀ : derivedPushforwardModule g L ≅ (DerivedCategory.singleFunctor T.Modules 0).obj E₀ :=
    e ≪≫ (DerivedCategory.singleFunctor T.Modules 0).mapIso
      (pushforwardIsoOfIsoSingle e).symm
  have hE₀ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E₀ :=
    (Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso
      (pushforwardIsoOfIsoSingle e).symm hE).isFiniteLocallyFree
  have hLs : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL
  have hLF := isFinitePresentation_and_isFlatOver_of_isInvertible g L hLs
  let ebc := (baseChangeDerivedPushforward g a g' q hsq hfp inferInstance L hLF.1 hLF.2).some
  let e' : derivedPushforwardModule g' ((Scheme.Modules.pullback q).obj L) ≅
      (DerivedCategory.singleFunctor T'.Modules 0).obj ((Scheme.Modules.pullback a).obj E₀) :=
    ebc.symm ≪≫ (derivedPullback a.toLRSHom.toShHom).mapIso e₀ ≪≫
      flatSinglePullbackIso a.toLRSHom.toShHom E₀
        (SheafOfModules.isFlat_of_isFiniteLocallyFree _ hE₀) 0
  exact (pushforwardIsoOfIsoSingle e').symm

end M9Native.PoincareChern.OrdinaryDegreeZero

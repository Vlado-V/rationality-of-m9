/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyTwistedEuler
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedCohomologyAlongRingMap
public import StacksFrontier.AlgebraicGeometry.Quot.GraphAmbientTensorAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange

/-!
# The actual scalar and Euler comparison for represented graph fibres

The field projection is the original scheme morphism underlying the
specified native morphism. The native scalar map is its actual
`smallerBaseRingHom`. Their compatibility is proved on the identity
chart, and the native cohomology comparison consequently retains the
original field scalar structure.

The scalar proof follows the native general argument used for the
projective-space specialization in
`Quot/ProjectiveQuotOverSpace/HilbertPolynomialComparison.lean`.
The original source is pinned with hashes in the accompanying audit.
No relation to a relative O(1), numerical degree, or Hilbert polynomial
is imposed by these definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace M9Native.GraphHilbertEulerComparison
open AlgebraicGeometry.Space

attribute [local instance] abelianRepresentedStructureRingSheafAlong
  enoughInjectives_representedModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : BigFppfOver B S hS) (k : Type u) [Field k]
  (hk : B.Contains (Spec (.of k))) (g : B.obj hk ⟶ B.obj hS)
  (w : U ⟶ Over.mk g)

/-- The same original scheme's actual morphism to the field. -/
abbrev originalProjection :
    (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (.of k) :=
  (BigFppfOver.toScheme B S hS).map w

/-- The native field action is induced by that actual projection. -/
abbrev nativeFieldScalar :=
  smallerBaseRingHom B S hS (schemeSpace U) k hk g (schemeSpaceMap w).hom

/-- The original scalar map is exactly the one in cohomologyOverField. -/
abbrev originalFieldScalar :
    k →+* ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫
    (originalProjection B S hS U k hk g w).appLE ⊤ ⊤ (by simp)).hom

/-- The identity chart recovers the actual native scheme morphism. -/
theorem chartToScheme_idChart :
    chartToScheme B S hS (schemeSpace U).1 (schemeSpaceMap w).hom
      (idChart B S hS U) = w := by
  apply Yoneda.fullyFaithful.map_injective
  simp only [chartToScheme, Functor.FullyFaithful.map_preimage]
  exact Category.id_comp _

/-- Both scalar actions agree on the original open top. No scalar or
projection compatibility is assumed. -/
theorem nativeFieldScalar_compatible (a : k) :
    (representedSchemeStructureSheaf B S hS U).obj.map
      (representedTopToIdChartAlong B S hS U).op
      ((Stacks.Cohomology.SiteModules.globalSectionEval
        (representedStructureRingSheaf B S hS U) (op (idChart B S hS U)))
        (nativeFieldScalar B S hS U k hk g w a)) =
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op ⊤)
          (originalFieldScalar B S hS U k hk g w a) := by
  have key : ∀ x, (representedSchemeStructureSheaf B S hS U).obj.map
      (representedTopToIdChartAlong B S hS U).op x =
        (Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
          (representedTopToIdChartAlong B S hS U).hom.left).op).hom x := fun _ => rfl
  refine (key _).trans ?_
  rw [representedTopToIdChartAlong_hom_left]
  have hev :
      (Stacks.Cohomology.SiteModules.globalSectionEval
        (representedStructureRingSheaf B S hS U) (op (idChart B S hS U)))
          (nativeFieldScalar B S hS U k hk g w a) =
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartToScheme B S hS (schemeSpace U).1 (schemeSpaceMap w).hom
            (idChart B S hS U))).op).hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom a) := rfl
  rw [hev, chartToScheme_idChart]
  have hcomp : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map w).op ≫
      Scheme.Γ.map ((⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι).op =
      (originalProjection B S hS U k hk g w).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.Opens.topIso (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)).inv := by
    simp only [Scheme.Γ_map_op, Scheme.Hom.appLE, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_inv, Scheme.Hom.appTop]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (_ ≫ ·) ?_
    refine Eq.trans ?_
      (((BigFppfOver.toScheme B S hS).obj U).presheaf.map_comp _ _)
    exact congrArg ((BigFppfOver.toScheme B S hS).obj U).presheaf.map
      (Subsingleton.elim _ _)
  exact congrArg (fun f => ((Scheme.ΓSpecIso (.of k)).inv ≫ f).hom a) hcomp

/-- The literal associated module used by the native arbitrary-base
cohomology comparison. -/
abbrev associatedModule (F : ((BigFppfOver.toScheme B S hS).obj U).Modules) :=
  (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj F)

/-- Native Euler characteristic along the actual field projection is
the original scheme Euler characteristic, with the same field scalars. -/
theorem eulerCharacteristicAlong_associated_eq
    (F : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hF : SheafOfModules.IsQuasicoherent F) :
    eulerCharacteristicAlong B S hS (schemeSpace U).1 (schemeSpace U).2 k
      (nativeFieldScalar B S hS U k hk g w) (associatedModule B S hS U F) =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank k
          (cohomologyOverField k (originalProjection B S hS U k hk g w) F i) : ℤ) := by
  refine (eulerCharacteristicAlong_eq_finsum_rightDerived B S hS _ _ k _ _).trans ?_
  refine finsum_congr fun i => ?_
  have hd :=
    ((representedCohomologyAssociatedModuleIsoAlong B S hS U k
      (nativeFieldScalar B S hS U k hk g w)
      (originalFieldScalar B S hS U k hk g w)
      (nativeFieldScalar_compatible B S hS U k hk g w) F hF i).toLinearEquiv.trans
        ULift.moduleEquiv).finrank_eq
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ i * (n : ℤ)) hd

/-- The actual Zariski reading on the original scheme, along its identity
chart. This is the reading used by `baseChangeModule`. -/
abbrev schemeReading
    (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  restrictToChartScheme B S hS (schemeSpace U).1 (schemeSpace U).2 N
    (idEtaleChart B S hS U)

/-- Quasi-coherence of that reading is a theorem of chart restriction. -/
theorem schemeReading_quasicoherent
    (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hN : N.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent (schemeReading B S hS U N) :=
  isQuasicoherent_restrictToChartScheme B S hS (schemeSpace U) N hN
    (idEtaleChart B S hS U)

/-- A quasi-coherent native module is the associated module of its
literal Zariski reading. No module comparison is an input. -/
def associatedSchemeReadingIso
    (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hN : N.IsQuasicoherentOnSite) :
    associatedModule B S hS U (schemeReading B S hS U N) ≅ N :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS U).functor).mapIso
      (restrictToChartSchemeIdEtaleChartIso B S hS U N) ≪≫
  (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
    (associatedModuleRestrictModuleIsoSelf
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)
      (isQuasicoherentOnSite_representedSmallEtaleModuleInverse N hN)) ≪≫
  (representedSmallEtaleModuleEquivalence B S hS U).counitIso.app N

/-- Native cohomology of a quasi-coherent module and original scheme
cohomology of its literal reading are isomorphic over the actual field. -/
def cohomologySchemeReadingIso
    (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hN : N.IsQuasicoherentOnSite) (i : ℕ) :
    (ModuleCat.restrictScalars.{u + 1} (nativeFieldScalar B S hS U k hk g w)).obj
      (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (representedStructureRingSheaf B S hS U)).rightDerived i).obj N) ≅
    (ModuleCat.uliftFunctor.{u + 1} k).obj
      (cohomologyOverField k (originalProjection B S hS U k hk g w)
        (schemeReading B S hS U N) i) :=
  (ModuleCat.restrictScalars.{u + 1} (nativeFieldScalar B S hS U k hk g w)).mapIso
    (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS U)).rightDerived i).mapIso
        (associatedSchemeReadingIso B S hS U N hN).symm) ≪≫
  representedCohomologyAssociatedModuleIsoAlong B S hS U k
    (nativeFieldScalar B S hS U k hk g w)
    (originalFieldScalar B S hS U k hk g w)
    (nativeFieldScalar_compatible B S hS U k hk g w)
    (schemeReading B S hS U N) (schemeReading_quasicoherent B S hS U N hN) i

/-- The Euler characteristic of any quasi-coherent native module is the
Euler characteristic of its original Zariski reading, with the actual
field scalars. -/
theorem eulerCharacteristicAlong_eq_schemeReading
    (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hN : N.IsQuasicoherentOnSite) :
    eulerCharacteristicAlong B S hS (schemeSpace U).1 (schemeSpace U).2 k
      (nativeFieldScalar B S hS U k hk g w) N =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank k
          (cohomologyOverField k (originalProjection B S hS U k hk g w)
            (schemeReading B S hS U N) i) : ℤ) := by
  exact (eulerCharacteristicAlong_congr B S hS _ _ k _
    (associatedSchemeReadingIso B S hS U N hN).symm).trans
      (eulerCharacteristicAlong_associated_eq B S hS U k hk g w
        (schemeReading B S hS U N) (schemeReading_quasicoherent B S hS U N hN))

section ReadingPowers

variable (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
  [hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (schemeSpace U).1)
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O).property N]

/-- The original reading of an invertible native module is invertible,
by the derived associated-module comparison and reflection in 03DX. -/
instance schemeReading_isInvertible :
    SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj U).presheaf
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.property
        (schemeReading B S hS U N) := by
  have hNq := isQuasicoherentOnSite_of_isInvertible B S hS (schemeSpace U) N
    hN.toAlgebraicGeometry
  have hA := @Stacks.SheafOfModules.isInvertible_of_iso.{u, u + 1, u}
    (SmallEtale B S hS (schemeSpace U).1) _ (SmallEtale.topology B S hS (schemeSpace U).1)
    (structurePresheaf B S hS (schemeSpace U).1)
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O).property _ _ _ _
    (associatedSchemeReadingIso B S hS U N hNq).symm hN
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (isInvertible_of_isInvertible_representedAssociatedModule B S hS U _
      (schemeReading_quasicoherent B S hS U N hNq) hA)

/-- Every integer tensor power of the actual original reading. -/
def schemeReadingTensorPower (n : ℤ) : ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower
    ((BigFppfOver.toScheme B S hS).obj U).presheaf
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.property
    (schemeReading B S hS U N) n

/-- The associated module of each original integer power is the actual
native integer power. The line comparison is constructed, not assumed. -/
def associatedSchemeReadingTensorPowerIso (n : ℤ) :
    associatedModule B S hS U (schemeReadingTensorPower B S hS U N n) ≅
      invertibleTensorPower B S hS (schemeSpace U).1 (schemeSpace U).2 N n := by
  have hNq := isQuasicoherentOnSite_of_isInvertible B S hS (schemeSpace U) N
    hN.toAlgebraicGeometry
  haveI : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (schemeSpace U).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O).property
      (associatedModule B S hS U (schemeReading B S hS U N)) :=
    @Stacks.SheafOfModules.isInvertible_of_iso.{u, u + 1, u}
      (SmallEtale B S hS (schemeSpace U).1) _ (SmallEtale.topology B S hS (schemeSpace U).1)
      (structurePresheaf B S hS (schemeSpace U).1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O).property _ _ _ _
      (associatedSchemeReadingIso B S hS U N hNq).symm hN
  exact representedAssociatedModuleTensorPowerIso B S hS U (schemeReading B S hS U N) n ≪≫
    invertibleTensorPowerCongr B S hS (schemeSpace U).1 (schemeSpace U).2
      (associatedSchemeReadingIso B S hS U N hNq) n

/-- The actual native powers and the actual original line powers have
the same Euler characteristics, for every integer, over the actual field. -/
theorem eulerCharacteristicAlong_tensorPower_eq_schemeReading (n : ℤ) :
    eulerCharacteristicAlong B S hS (schemeSpace U).1 (schemeSpace U).2 k
      (nativeFieldScalar B S hS U k hk g w)
      (invertibleTensorPower B S hS (schemeSpace U).1 (schemeSpace U).2 N n) =
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
      (Module.finrank k (cohomologyOverField k (originalProjection B S hS U k hk g w)
        (schemeReadingTensorPower B S hS U N n) i) : ℤ) := by
  exact (eulerCharacteristicAlong_congr B S hS _ _ k _
    (associatedSchemeReadingTensorPowerIso B S hS U N n).symm).trans
      (eulerCharacteristicAlong_associated_eq B S hS U k hk g w _
        (@Scheme.Modules.isQuasicoherent_tensorPower_of_isInvertible _
          (schemeReading B S hS U N) inferInstance n))

end ReadingPowers

variable {B S hS U k hk g}

/-- The original scheme projection obtained from the actual projection
of a native space represented by `U`. -/
def projectionOfIso {W : AlgebraicSpaces B S hS}
    (E : schemeSpace U ≅ W) (q : W.1 ⟶ yoneda.obj (Over.mk g)) :
    U ⟶ Over.mk g :=
  yoneda.preimage (E.hom.hom ≫ q)

theorem projectionOfIso_inv_comp {W : AlgebraicSpaces B S hS}
    (E : schemeSpace U ≅ W) (q : W.1 ⟶ yoneda.obj (Over.mk g)) :
    E.inv.hom ≫ (schemeSpaceMap (projectionOfIso E q)).hom = q := by
  rw [projectionOfIso, show (schemeSpaceMap
    (yoneda.preimage (E.hom.hom ≫ q))).hom = E.hom.hom ≫ q from
      yoneda.map_preimage _]
  rw [← Category.assoc]
  exact (congrArg (fun f => f.hom ≫ q) E.inv_hom_id).trans (Category.id_comp q)

/-- An actual invertible native module on an isomorphic represented
space has the original scheme Euler characteristic of its restriction.
Both the projection and scalar compatibility are derived from `E`. -/
theorem eulerCharacteristicAlong_iso_eq_schemeReading
    {W : AlgebraicSpaces B S hS} (E : schemeSpace U ≅ W)
    (q : W.1 ⟶ yoneda.obj (Over.mk g))
    (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS W.1 W.2)
    (hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS W.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O).property N) :
    eulerCharacteristicAlong B S hS W.1 W.2 k
      (smallerBaseRingHom B S hS W k hk g q) N =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        (Module.finrank k (cohomologyOverField k
          (originalProjection B S hS U k hk g (projectionOfIso E q))
          (schemeReading B S hS U ((modulePullback B S hS E.hom).obj N)) i) : ℤ) := by
  have hNq : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS W N hN.toAlgebraicGeometry
  have hPN := isQuasicoherentOnSite_modulePullback_of_isInvertible E.hom N hN
  have hc : GlobalSectionRingHomsCompatible B S hS E.inv
      (relativelyRepresentable_of_isAffineHom B S hS E.inv (isAffineHom_of_isIso E.inv.hom))
      (nativeFieldScalar B S hS U k hk g (projectionOfIso E q))
      (smallerBaseRingHom B S hS W k hk g q) := by
    change GlobalSectionRingHomsCompatible B S hS E.inv _
      ((globalSectionsRingHom B S hS (schemeSpace U).1 (schemeSpace U).2
        (schemeSpaceMap (projectionOfIso E q)).hom).comp (Scheme.ΓSpecIso (.of k)).inv.hom)
      ((globalSectionsRingHom B S hS W.1 W.2 q).comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    simpa only [projectionOfIso_inv_comp] using
      (globalSectionRingHomsCompatible_globalSectionsRingHom B S hS E.inv _
        (schemeSpaceMap (projectionOfIso E q)).hom (Scheme.ΓSpecIso (.of k)).inv.hom)
  exact (eulerCharacteristicAlong_modulePullback_of_iso E k _ _ hc N hNq).symm.trans
    (eulerCharacteristicAlong_eq_schemeReading B S hS U k hk g
      (projectionOfIso E q) _ hPN)

section Graph

variable {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
  (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
  (hQ : IsAlgebraicSpace B S hS Q)
  (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
  (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
  (hz : yoneda.relativelyRepresentable z)
  {T : BigFppfOver B S hS} (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T))

/-- The actual scheme representing the source of the relative morphism
after its test-scheme base change. -/
abbrev graphSourceScheme : BigFppfOver B S hS := hz.pullback p.base

/-- The actual Hilbert family of the native graph. -/
def actualGraphFamily : HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T :=
  ⟨p.base, graphHilbertFamily hZ hX hQ p hsep hfp hflat hproper⟩

/-- The original source represents the actual graph support. The
isomorphism is constructed from representability and the graph's mono. -/
def graphSupportIso :
    schemeSpace (graphSourceScheme hz p) ≅
      (actualGraphFamily hZ hX hQ hsep hfp hflat hproper p).subspace :=
  ObjectProperty.isoMk _ ((hz.isPullback p.base).flip.isoPullback ≪≫
    asIso (Subfunctor.toRange (graphMap p)))

theorem graphSupportIso_projection :
    (graphSupportIso hZ hX hQ hsep hfp hflat hproper hz p).hom ≫
      (actualGraphFamily hZ hX hQ hsep hfp hflat hproper p).subspaceInclusion ≫
        schemeBaseChangeProjectionHom B S hS (graphAmbientMap B S hS z x hZ hX hQ)
          (CostructuredArrow.mk p.base) = schemeSpaceMap (hz.snd p.base) := by
  apply ObjectProperty.hom_ext
  change ((hz.isPullback p.base).flip.isoPullback.hom ≫
      Subfunctor.toRange (graphMap p)) ≫
    (Subfunctor.range (graphMap p)).ι ≫
      pullback.snd (pullback.fst z x ≫ z) p.base = yoneda.map (hz.snd p.base)
  rw [Category.assoc, Subfunctor.toRange_ι_assoc, graphMap_snd]
  exact (hz.isPullback p.base).flip.isoPullback_hom_fst

/-- The actual original source map to the graph ambient space. -/
def graphAmbientFromSource :
    yoneda.obj (graphSourceScheme hz p) ⟶ (graphAmbient B S hS z x hZ hX hQ).1 :=
  (graphSupportIso hZ hX hQ hsep hfp hflat hproper hz p).hom.hom ≫
    (actualGraphFamily hZ hX hQ hsep hfp hflat hproper p).subspaceInclusion.hom ≫
      pullback.fst (pullback.fst z x ≫ z) p.base

theorem graphAmbientFromSource_fst :
    graphAmbientFromSource hZ hX hQ hsep hfp hflat hproper hz p ≫ pullback.fst z x =
      hz.fst p.base := by
  change ((hz.isPullback p.base).flip.isoPullback.hom ≫
      Subfunctor.toRange (graphMap p)) ≫
    (Subfunctor.range (graphMap p)).ι ≫
      pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.fst z x = hz.fst p.base
  rw [Category.assoc, Subfunctor.toRange_ι_assoc, graphMap_fst_fst]
  exact (hz.isPullback p.base).flip.isoPullback_hom_snd

theorem graphAmbientFromSource_snd :
    graphAmbientFromSource hZ hX hQ hsep hfp hflat hproper hz p ≫ pullback.snd z x =
      (hz.isPullback p.base).flip.isoPullback.hom ≫ p.morphism := by
  change ((hz.isPullback p.base).flip.isoPullback.hom ≫
      Subfunctor.toRange (graphMap p)) ≫
    (Subfunctor.range (graphMap p)).ι ≫
      pullback.fst (pullback.fst z x ≫ z) p.base ≫ pullback.snd z x = _
  rw [Category.assoc, Subfunctor.toRange_ι_assoc, graphMap_fst_snd]

variable (N : AlgebraicGeometry.Space.Modules.{u, u} B S hS Z hZ)
  (L : AlgebraicGeometry.Space.Modules.{u, u} B S hS X hX)
  [hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z hZ).O).property N]
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O).property L]

/-- The actual restricted graph polarization is the tensor product of
the two actual original scheme readings. No line identification is an
input to this isomorphism. -/
def graphPolarizationTensorIso :
    baseChangeModule B S hS (graphAmbientTensor z x hZ hX hQ N L)
      (graphSourceScheme hz p) (graphAmbientFromSource hZ hX hQ hsep hfp hflat hproper hz p) ≅
    Stacks.RelativeVeryAmple.tensorModules _
      (baseChangeModule B S hS (X := ⟨Z, hZ⟩) N (graphSourceScheme hz p) (hz.fst p.base))
      (baseChangeModule B S hS (X := ⟨X, hX⟩) L (graphSourceScheme hz p)
        ((hz.isPullback p.base).flip.isoPullback.hom ≫ p.morphism)) :=
  baseChangeModuleGraphAmbientTensorIso N L (graphSourceScheme hz p)
    (graphAmbientFromSource hZ hX hQ hsep hfp hflat hproper hz p) ≪≫
  Stacks.RelativeVeryAmple.tensorModulesMapIso _
    (eqToIso (congrArg (baseChangeModule B S hS (X := ⟨Z, hZ⟩) N (graphSourceScheme hz p))
      (graphAmbientFromSource_fst hZ hX hQ hsep hfp hflat hproper hz p)))
    (eqToIso (congrArg (baseChangeModule B S hS (X := ⟨X, hX⟩) L (graphSourceScheme hz p))
      (graphAmbientFromSource_snd hZ hX hQ hsep hfp hflat hproper hz p)))

end Graph
end M9Native.GraphHilbertEulerComparison

module

public import M9StacksIntegration.FieldBaseChangeRank
public import Mathlib.Algebra.Field.Equiv
public import M9StacksIntegration.SpecFieldPullbackSections
public import M9StacksIntegration.MukaiSaturationRank
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackMonoDualMap

/-! Ranks at actual field-valued points. The actual section map of a
pullback is compared with its sole stalk through the original germ map,
then with the original stalk map by the natural native pullback/stalk
isomorphism. Residue-field extension preserves the actual linear image.
No local freeness or supplied fiber comparison is an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.ModuleSkyscraper.modulesStalkFunctor Stacks.ModuleSkyscraper.presheafStalkFunctor

namespace M9Native.FieldPointMapRank

open SpecFieldStalkSections SpecFieldPullbackSections FieldBaseChangeRank
open Stacks.ModuleSkyscraper

variable (K : Type u) [Field K]

@[instance_reducible] def localRingField : Field (localRing K) :=
  ((scalarStalkEquiv K).symm.isField (Field.toIsField K)).toField

attribute [local instance] localRingField

local instance stalkBModule (M : (space K).Modules) :
    Module (localRing K) (M.presheaf.stalk (point K)) :=
  Stacks.ModuleStalkSpecialization.stalkModule M (point K)

local instance stalkKModule (M : (space K).Modules) :
    Module K (M.presheaf.stalk (point K)) := moduleStalk K M

local instance stalkTower (M : (space K).Modules) :
    IsScalarTower K (localRing K) (M.presheaf.stalk (point K)) :=
  stalkScalarTower K M

local instance nativeStalkKModule (M : (space K).Modules) :
    Module K ((modulesStalkFunctor (space K) (point K)).obj M) := by
  change Module K (M.presheaf.stalk (point K))
  exact moduleStalk K M

local instance nativeStalkTower (M : (space K).Modules) :
    IsScalarTower K (localRing K) ((modulesStalkFunctor (space K) (point K)).obj M) := by
  change IsScalarTower K (localRing K) (M.presheaf.stalk (point K))
  exact stalkScalarTower K M

def stalkKMap {M N : (space K).Modules} (a : M ⟶ N) :
    M.presheaf.stalk (point K) →ₗ[K] N.presheaf.stalk (point K) :=
  ((modulesStalkFunctor (space K) (point K)).map a).hom.restrictScalars K

theorem sectionsStalkEquiv_naturality {M N : (space K).Modules} (a : M ⟶ N) :
    (stalkKMap K a).comp (sectionsStalkEquiv K M).toLinearMap =
      (sectionsStalkEquiv K N).toLinearMap.comp (moduleSpecΓFunctor.map a).hom := by
  ext s
  change ((modulesStalkFunctor (space K) (point K)).map a).hom
    (M.presheaf.germ ⊤ (point K) trivial s) =
      N.presheaf.germ ⊤ (point K) trivial (a.app ⊤ s)
  exact Stacks.Modules.stalkLinearMap_germ a.val ⊤ trivial s

theorem localRing_finrank : finrank K (localRing K) = 1 :=
  (scalarLinearEquiv K).finrank_eq.symm.trans (Module.finrank_self K)

theorem finrank_range_sections_eq_stalk {M N : (space K).Modules} (a : M ⟶ N) :
    finrank K (LinearMap.range (moduleSpecΓFunctor.map a).hom) =
      finrank (localRing K) (LinearMap.range
        ((modulesStalkFunctor (space K) (point K)).map a).hom) := by
  have he : (moduleSpecΓFunctor.map a).hom =
      (sectionsStalkEquiv K N).symm.toLinearMap.comp
        ((stalkKMap K a).comp (sectionsStalkEquiv K M).toLinearMap) := by
    ext s
    apply (sectionsStalkEquiv K N).injective
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using
      (LinearMap.congr_fun (sectionsStalkEquiv_naturality K a) s).symm
  calc
    finrank K (LinearMap.range (moduleSpecΓFunctor.map a).hom) =
        finrank K (LinearMap.range ((sectionsStalkEquiv K N).symm.toLinearMap.comp
          ((stalkKMap K a).comp (sectionsStalkEquiv K M).toLinearMap))) :=
      congrArg (fun t : moduleSpecΓFunctor.obj M →ₗ[K] moduleSpecΓFunctor.obj N =>
        finrank K (LinearMap.range t)) he
    _ = finrank K (LinearMap.range (stalkKMap K a)) :=
      finrank_range_equiv K (stalkKMap K a) (sectionsStalkEquiv K M) (sectionsStalkEquiv K N).symm
    _ = _ := finrank_range_restrictScalars K (localRing K)
      ((modulesStalkFunctor (space K) (point K)).map a).hom (localRing_finrank K)

variable {X : Scheme.{u}}

/-- Genuine field-point pullback sections compute the original residue
rank. The point may have any residue extension into the chosen field. -/
theorem finrank_range_pullbackSections_eq_mapRankAt {M N : X.Modules}
    (a : M ⟶ N) (p : space K ⟶ X) :
    finrank K (LinearMap.range (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map a)).hom) =
      MukaiSemiIrreducible.mapRankAt a (p (point K)) := by
  let x : X := p (point K)
  let A := X.presheaf.stalk x
  let L := X.residueField x
  let B := localRing K
  let : Algebra A L := (X.residue x).hom.toAlgebra
  let : Algebra A B := (p.stalkMap (point K)).hom.toAlgebra
  let : Algebra L B := (X.descResidueField (p.stalkMap (point K))).hom.toAlgebra
  let : IsScalarTower A L B := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => rfl)
  let e := pullbackStalkIso p (point K)
  have hfac :
      ((modulesStalkFunctor (space K) (point K)).map ((Scheme.Modules.pullback p).map a)) =
      (e.app M).inv ≫
        ((modulesStalkFunctor X x ⋙ ModuleCat.extendScalars (p.stalkMap (point K)).hom).map a) ≫
          (e.app N).hom := by
    have hn :
        ((modulesStalkFunctor X x ⋙ ModuleCat.extendScalars (p.stalkMap (point K)).hom).map a) ≫
          (e.app N).hom =
        (e.app M).hom ≫
          ((modulesStalkFunctor (space K) (point K)).map ((Scheme.Modules.pullback p).map a)) :=
      e.hom.naturality a
    have hh := congrArg (fun t => (e.app M).inv ≫ t) hn
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh.symm
  have hlin :
      ((modulesStalkFunctor (space K) (point K)).map ((Scheme.Modules.pullback p).map a)).hom =
      (e.app N).toLinearEquiv.toLinearMap.comp
        ((((modulesStalkFunctor X x).map a).hom.baseChange B).comp
          (e.app M).toLinearEquiv.symm.toLinearMap) := by
    exact congrArg ModuleCat.Hom.hom hfac
  calc
    _ = finrank B (LinearMap.range
        ((modulesStalkFunctor (space K) (point K)).map ((Scheme.Modules.pullback p).map a)).hom) :=
      finrank_range_sections_eq_stalk K _
    _ = finrank B (LinearMap.range (((modulesStalkFunctor X x).map a).hom.baseChange B)) := by
      rw [hlin]
      exact finrank_range_equiv B _ _ _
    _ = finrank L (LinearMap.range (((modulesStalkFunctor X x).map a).hom.baseChange L)) :=
      finrank_range_baseChange_tower L B _
    _ = _ := by
      rfl

end M9Native.FieldPointMapRank

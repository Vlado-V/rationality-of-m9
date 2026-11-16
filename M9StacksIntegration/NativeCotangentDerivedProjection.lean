module

public import M9StacksIntegration.NativeCotangentPushProjection
public import M9StacksIntegration.NativeCotangentDifferentialMap
public import M9StacksIntegration.DirectCotangentComparison
public import M9StacksIntegration.StandardCotangentArrow

/-!
# The original direct cotangent arrow has the literal differential normalization

The original chain projection square and the naturality of the exact
original derived comparison prove the derived square. Original smooth
normalization and single-functor faithfulness then identify its actual
sheaf map with the literal native scheme differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.NativeCotangentDerivedProjection

namespace Ringed

variable {X Y S : RingedSpace.{u,u}} (g : X ⟶ Y) (f : Y ⟶ S)

/-- The original direct derived map commutes with the original actual
cotangent projections, before any smoothness assumption. -/
theorem derived_projection_square :
    derivedPullbackNaiveCotangentMap g f ≫ DerivedCategory.Q.map
      (StandardSmoothCotangentProjection.Ringed.complexProjection (g ≫ f)) =
    (derivedPullback g).map (DerivedCategory.Q.map
      (StandardSmoothCotangentProjection.Ringed.complexProjection f)) ≫
      derivedPullbackSingleObj g
        (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)) ≫
      (DerivedCategory.singleFunctor (RingedSpace.siteModules X) 0).map
        (NativeCotangentPushProjection.pullbackDifferentialMap g f) := by
  rw [DirectCotangentComparison.directMap_eq]
  rw [Category.assoc, ← Functor.map_comp,
    NativeCotangentPushProjection.pullback_projection_square]
  simp only [Functor.map_comp]
  rw [← DirectCotangentComparison.comparison_naturality_assoc]
  let F := AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)
  let v := DerivedCategory.Q.map
    ((CochainComplex.singleFunctor (RingedSpace.siteModules X) 0).map
      (NativeCotangentPushProjection.pullbackDifferentialMap g f))
  have hs := DirectCotangentComparison.comparison_single g F
  have ht : (DirectCotangentComparison.comparisonNat g).app
        ((CochainComplex.singleFunctor (RingedSpace.siteModules Y) 0).obj F) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback g)
          (ComplexShape.up ℤ) 0).hom.app F) ≫ v =
      derivedPullbackSingleObj g F ≫ v :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ v) hs)
  have hv : v = (DerivedCategory.singleFunctor (RingedSpace.siteModules X) 0).map
      (NativeCotangentPushProjection.pullbackDifferentialMap g f) := rfl
  exact (congrArg (fun z => (derivedPullback g).map (DerivedCategory.Q.map
      (StandardSmoothCotangentProjection.Ringed.complexProjection f)) ≫ z) ht).trans
    (congrArg (fun z => (derivedPullback g).map (DerivedCategory.Q.map
      (StandardSmoothCotangentProjection.Ringed.complexProjection f)) ≫
        derivedPullbackSingleObj g F ≫ z) hv)

end Ringed

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y)
  [Smooth pY] [Smooth (g ≫ pY)]

omit [Smooth pY] [Smooth (g ≫ pY)] in
private theorem pullbackDifferentialMap_scheme_eq :
    NativeCotangentPushProjection.pullbackDifferentialMap
      g.toLRSHom.toShHom pY.toLRSHom.toShHom =
      NativeCotangentDifferentialMap.directMap g pY := rfl

omit [Smooth pY] [Smooth (g ≫ pY)] in
private theorem singleMap_scheme_eq {A B : X.Modules} (h : A ⟶ B) :
    (DerivedCategory.singleFunctor (RingedSpace.siteModules X.toRingedSpace) 0).map h =
      (DerivedCategory.singleFunctor X.Modules 0).map h := rfl

omit [Smooth pY] [Smooth (g ≫ pY)] in
private theorem derivedPullbackSingleObj_scheme_eq :
    derivedPullbackSingleObj g.toLRSHom.toShHom
      (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap pY.toLRSHom.toShHom)) =
      derivedPullbackSingleObj g.toLRSHom.toShHom (Scheme.Hom.relativeDifferentials pY) := rfl

/-- Actual original smooth normalization of the literal direct cotangent
arrow gives the literal native differential map. -/
theorem normalizedMap_eq :
    StandardCotangentArrow.normalizedMap (g ≫ pY) pY g
      (derivedPullbackNaiveCotangentMap g.toLRSHom.toShHom pY.toLRSHom.toShHom) =
    Scheme.Hom.relativeDifferentialsMap g pY (g ≫ pY) (𝟙 _) (by simp) := by
  rw [← NativeCotangentDifferentialMap.directMap_eq]
  apply (DerivedCategory.singleFunctor X.Modules 0).map_injective
  rw [StandardCotangentArrow.single_map_normalizedMap]
  apply (cancel_epi (StandardSmoothCotangent.pulledDifferentialsIso pY g).hom).mp
  rw [Iso.hom_inv_id_assoc]
  rw [StandardSmoothCotangent.pulledDifferentialsIso_hom]
  rw [← StandardSmoothCotangentProjection.derivedProjection_eq pY,
    ← StandardSmoothCotangentProjection.derivedProjection_eq (g ≫ pY)]
  simpa only [StandardSmoothCotangentProjection.complexProjection,
    Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom,
    pullbackDifferentialMap_scheme_eq, singleMap_scheme_eq,
    derivedPullbackSingleObj_scheme_eq, Category.assoc] using
    Ringed.derived_projection_square g.toLRSHom.toShHom pY.toLRSHom.toShHom

end M9Native.NativeCotangentDerivedProjection

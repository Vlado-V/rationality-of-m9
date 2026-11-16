module

public import M9StacksIntegration.NativeCotangentPushCoordinates
public import M9StacksIntegration.NativeCotangentProjection
public import M9StacksIntegration.AdjointCochainProjection

/-!
# The original direct cotangent map commutes with the original projections

The native actual cokernel square is transposed through the original
adjunction. Every projection and the final site-to-native transport is
retained literally; no cochain covariance equation is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpaceThickening RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace M9Native.NativeCotangentPushProjection

variable {X Y S : RingedSpace.{u,u}} (g : X ⟶ Y) (f : Y ⟶ S)

/-- The actual adjoint of the checked original native differential map. -/
def pullbackDifferentialMap :=
  ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm
    (NativeCotangentPushCoordinates.differentialsMap g f)

private theorem baseRing_eq {T U : RingedSpace.{u,u}} (h : T ⟶ U) :
    AlgebraicGeometry.RingedSpaceThickening.inverseImageBaseRing h =
      Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf h := rfl

private theorem ringMap_eq {T U : RingedSpace.{u,u}} (h : T ⟶ U) :
    AlgebraicGeometry.RingedSpaceThickening.structureRingMap h =
      Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap h := rfl

private theorem originalG_map_eq
    {M N : SheafOfModules.{u} (structureSheafRing X)} (a : M ⟶ N) :
    (NativeCotangentPushCoordinates.originalG g).map a = (modulePushforward g).map a := rfl

/-- The actual direct adjoint chain map commutes with the original
chain projections, by the proved native cokernel square. -/
theorem pullback_projection_square :
    pullbackNaiveCotangentMap g f ≫
      StandardSmoothCotangentProjection.Ringed.complexProjection (g ≫ f) =
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (StandardSmoothCotangentProjection.Ringed.complexProjection f) ≫
      (HomologicalComplex.singleMapHomologicalComplex (modulePullback g)
        (ComplexShape.up ℤ) 0).hom.app _ ≫
      (CochainComplex.singleFunctor (RingedSpace.siteModules X) 0).map
        (pullbackDifferentialMap g f) := by
  let p := StandardSmoothCotangentProjection.Ringed.complexProjection f
  let q := StandardSmoothCotangentProjection.Ringed.complexProjection (g ≫ f)
  have hk : p.f 0 ≫
      (HomologicalComplex.singleObjXSelf (V := RingedSpace.siteModules Y)
        (ComplexShape.up ℤ) 0 _).hom ≫ NativeCotangentPushCoordinates.differentialsMap g f =
    (NativeCotangentPushCoordinates.nativeChain g f).f 0 ≫ (modulePushforward g).map
      (q.f 0 ≫ (HomologicalComplex.singleObjXSelf (V := RingedSpace.siteModules X)
        (ComplexShape.up ℤ) 0 _).hom) := by
    have h := NativeCotangentPushCoordinates.differentials_projection_square g f
    simpa only [p, q, NativeCotangentProjection.Ringed.complexProjection_f_zero,
      NativeCotangentPushCoordinates.siteComplex, NativeCotangentPushCoordinates.siteCokerIso,
      NativeCotangentPushCoordinates.siteDifferentialsIso,
      NativeCotangentPushCoordinates.nativeChain_eq,
      RingedSpace.naiveCotangentComplex, baseRing_eq, ringMap_eq,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
      originalG_map_eq] using h
  have h := AdjointCochainProjection.transpose_projection_square
    (modulePullbackPushforwardAdjunction g)
    (NativeCotangentPushCoordinates.nativeChain g f) p q
    (NativeCotangentPushCoordinates.differentialsMap g f) hk
  have hc : ((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
      (ComplexShape.up ℤ)).homEquiv _ _).symm
      (NativeCotangentPushCoordinates.nativeChain g f) = pullbackNaiveCotangentMap g f :=
    congrArg (((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
      (ComplexShape.up ℤ)).homEquiv _ _).symm)
      (NativeCotangentPushCoordinates.nativeChain_eq g f)
  exact (congrArg (fun a => a ≫ q) hc.symm).trans h

end M9Native.NativeCotangentPushProjection

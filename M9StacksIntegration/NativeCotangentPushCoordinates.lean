module

public import M9StacksIntegration.NativeCotangentPushGenerators
public import M9StacksIntegration.CotangentChainDifferentials
public import M9StacksIntegration.NativeCotangentProjection

/-! Actual site differential coordinates of the original native cotangent
push-map. Generic site coordinates are specialized before the native chain
is inserted, preserving the original coefficient categories and maps. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.SheafOfModules Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite universalDerivationOfSite)

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

universe u

namespace M9Native.NativeCotangentPushCoordinates

variable {X Y S : RingedSpace.{u,u}} (g : X ⟶ Y) (f : Y ⟶ S)

abbrev originalG := _root_.SheafOfModules.pushforward.{u}
  (pushforwardRingHom g.hom.base (structureComorphism g))

abbrev siteComplex := naiveCotangentComplex.{u,u,u,u}
  (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing f) Y.sheaf (structureRingMap f)

abbrev siteDifferentials := moduleOfDifferentialsOfSite.{u,u,u,u}
  (inverseImageBaseRing f) Y.sheaf (structureRingMap f)

abbrev ChainType := siteComplex f ⟶
  ((originalG g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (siteComplex (g ≫ f))

/-- The actual native map, retained as a single typed chain term. -/
@[irreducible] def nativeChain : ChainType g f := by
  change PresentedSquareZeroExtension.relativeComplex f ⟶
    ((originalG g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (PresentedSquareZeroExtension.relativeComplex (g ≫ f))
  exact naiveCotangentPushMap g f

theorem nativeChain_eq : nativeChain g f = naiveCotangentPushMap g f := by
  unfold nativeChain
  rfl

/-- Specialize the actual generic construction while the chain remains
an abstract argument. -/
@[irreducible] def siteMapOfChain :=
  CotangentChainDifferentials.differentialMap
    (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Y.carrier)
    (Opens.map g.hom.base)
    (inverseImageBaseRing (g ≫ f)) X.sheaf (structureRingMap (g ≫ f))
    (inverseImageBaseRing f) Y.sheaf (structureRingMap f)
    (pushforwardRingHom g.hom.base (structureComorphism g))

/-- Differential coordinates of the original native chain. -/
def siteMap := siteMapOfChain g f (nativeChain g f)

/-- The original native cokernel coordinates for site differentials. -/
abbrev siteCokerIso := naiveCotangentCokernelIso.{u,u,u,u}
  (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing f) Y.sheaf (structureRingMap f)

/-- The exact original projection square of the native push-map. -/
theorem projection_square :
    cokernel.π ((siteComplex f).d (-1) 0) ≫ (siteCokerIso f).hom ≫ siteMap g f =
      (naiveCotangentPushMap g f).f 0 ≫ (originalG g).map
        (cokernel.π ((siteComplex (g ≫ f)).d (-1) 0) ≫ (siteCokerIso (g ≫ f)).hom) := by
  have h := CotangentChainDifferentials.projection_square
    (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Y.carrier)
    (Opens.map g.hom.base)
    (inverseImageBaseRing (g ≫ f)) X.sheaf (structureRingMap (g ≫ f))
    (inverseImageBaseRing f) Y.sheaf (structureRingMap f)
    (pushforwardRingHom g.hom.base (structureComorphism g)) (nativeChain g f)
  simpa only [siteMap, siteMapOfChain, nativeChain_eq] using h

/-- On every open, the actual map sends d(b) to d(g#b). -/
theorem siteMap_d (U : (Opens Y.carrier)ᵒᵖ) (b : Y.sheaf.obj.obj U) :
    (siteMap g f).val.app U
        ((universalDerivationOfSite.{u,u,u,u} (inverseImageBaseRing f) Y.sheaf
          (structureRingMap f)).d b) =
      (universalDerivationOfSite.{u,u,u,u} (inverseImageBaseRing (g ≫ f)) X.sheaf
        (structureRingMap (g ≫ f))).d ((structureComorphism g).hom.app U b) := by
  have hv := NativeCotangentPushGenerators.pushMap_variableDifferential g f U b
  rw [← nativeChain_eq g f] at hv
  have h := CotangentChainDifferentials.differentialMap_d
    (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Y.carrier)
    (Opens.map g.hom.base)
    (inverseImageBaseRing (g ≫ f)) X.sheaf (structureRingMap (g ≫ f))
    (inverseImageBaseRing f) Y.sheaf (structureRingMap f)
    (pushforwardRingHom g.hom.base (structureComorphism g)) (nativeChain g f)
    U b ((structureComorphism g).hom.app U b) hv
  simpa only [siteMap, siteMapOfChain] using h

/-- The literal native equality transport from site to ringed differentials. -/
abbrev siteDifferentialsIso := NativeCotangentProjection.Ringed.siteDifferentialsIso f

/-- The original ringed-space differential map, with both native equality
transports retained explicitly. -/
def differentialsMap := (siteDifferentialsIso f).inv ≫ siteMap g f ≫
  (originalG g).map (siteDifferentialsIso (g ≫ f)).hom

/-- The original projection square after the literal native final transport. -/
theorem differentials_projection_square :
    cokernel.π ((siteComplex f).d (-1) 0) ≫ (siteCokerIso f).hom ≫
        (siteDifferentialsIso f).hom ≫ differentialsMap g f =
      (naiveCotangentPushMap g f).f 0 ≫ (originalG g).map
        (cokernel.π ((siteComplex (g ≫ f)).d (-1) 0) ≫
          (siteCokerIso (g ≫ f)).hom ≫ (siteDifferentialsIso (g ≫ f)).hom) := by
  have h := congrArg (fun z => z ≫ (originalG g).map
    (siteDifferentialsIso (g ≫ f)).hom) (projection_square g f)
  simpa only [differentialsMap, Iso.hom_inv_id_assoc, Category.assoc,
    Functor.map_comp] using h

/-- The native equality transport respects the actual universal derivation. -/
theorem siteDifferentialsIso_hom_d (U : (Opens Y.carrier)ᵒᵖ) (b : Y.sheaf.obj.obj U) :
    (siteDifferentialsIso f).hom.val.app U
        ((universalDerivationOfSite.{u,u,u,u} (inverseImageBaseRing f) Y.sheaf
          (structureRingMap f)).d b) =
      (AlgebraicGeometry.SheafOfModules.universalDerivation.{u,u,u}
        (structureRingMap f)).d b := by
  rfl

/-- The inverse native equality transport respects the actual derivation. -/
theorem siteDifferentialsIso_inv_d (U : (Opens Y.carrier)ᵒᵖ) (b : Y.sheaf.obj.obj U) :
    (siteDifferentialsIso f).inv.val.app U
        ((AlgebraicGeometry.SheafOfModules.universalDerivation.{u,u,u}
          (structureRingMap f)).d b) =
      (universalDerivationOfSite.{u,u,u,u} (inverseImageBaseRing f) Y.sheaf
        (structureRingMap f)).d b := by
  rfl

/-- On every open, the original ringed differential map has its actual
universal-derivation formula. -/
theorem differentialsMap_d (U : (Opens Y.carrier)ᵒᵖ) (b : Y.sheaf.obj.obj U) :
    (differentialsMap g f).val.app U
        ((AlgebraicGeometry.SheafOfModules.universalDerivation.{u,u,u}
          (structureRingMap f)).d b) =
      (AlgebraicGeometry.SheafOfModules.universalDerivation.{u,u,u}
        (structureRingMap (g ≫ f))).d ((structureComorphism g).hom.app U b) := by
  change (siteDifferentialsIso (g ≫ f)).hom.val.app
      ((Opens.map g.hom.base).op.obj U)
      ((siteMap g f).val.app U
        ((siteDifferentialsIso f).inv.val.app U
          ((AlgebraicGeometry.SheafOfModules.universalDerivation.{u,u,u}
            (structureRingMap f)).d b))) = _
  rw [siteDifferentialsIso_inv_d, siteMap_d, siteDifferentialsIso_hom_d]

end M9Native.NativeCotangentPushCoordinates

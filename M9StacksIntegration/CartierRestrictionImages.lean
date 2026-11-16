module

public import M9StacksIntegration.CartierRestrictionTensor
public import M9StacksIntegration.DirectC9Bundles
public import M9StacksIntegration.DirectImageTwoTerm
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# Genuine derived images of the actual Cartier restriction terms

The divisor projection is finite locally free. An actual restricted
line therefore has degree-zero derived image equal to its actual
ordinary pushforward. The tensor and normal-kernel comparisons below
use the true ordinary projection formula and true pullback-tensor
comparison. These are isomorphisms of the original derived images,
not equalities imposed on Grothendieck classes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace M9Native.CartierRestrictionImages

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory
  _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

variable {Y S : Scheme.{u}} (p : Y ⟶ S) (D : Y.IdealSheafData) (L : Y.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
  (r : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ p) r]

/-- The actual restricted line has its actual ordinary finite image
as its actual derived image, placed in degree zero. -/
def derivedClosedImageIso :
    derivedPushforwardModule p ((Scheme.Modules.pushforward D.subschemeι).obj
      ((Scheme.Modules.pullback D.subschemeι).obj L)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        ((Scheme.Modules.pushforward (D.subschemeι ≫ p)).obj
          ((Scheme.Modules.pullback D.subschemeι).obj L)) := by
  let Ld := (Scheme.Modules.pullback D.subschemeι).obj L
  letI hLd := Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj D.subschemeι L
  letI : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2 Ld :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hLd
  have hQ : Ld.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible Ld
  exact DirectImageTwoTerm.derivedPushforwardOfAffinePushforwardIso D.subschemeι p Ld hQ ≪≫
    DirectImageTwoTerm.derivedPushforwardIsoSinglePushforward (D.subschemeι ≫ p) Ld r
      (DirectC9Bundles.finiteFlat_line_hasDerivedRank (D.subschemeι ≫ p) r Ld)

/-- Actual tensor with the closed structure module has the retained
ordinary restriction image in degree zero. -/
def derivedTensorClosedImageIso :
    derivedPushforwardModule p
      (Scheme.Modules.tensorObj (Scheme.IdealSheafData.closedSubschemeStructureSheaf D) L) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        ((Scheme.Modules.pushforward (D.subschemeι ≫ p)).obj
          ((Scheme.Modules.pullback D.subschemeι).obj L)) :=
  (derivedPushforward p.toLRSHom.toShHom).mapIso
    ((DerivedCategory.singleFunctor Y.Modules 0).mapIso
      (CartierRestrictionTensor.tensorClosedStructureIso D L)) ≪≫
  derivedClosedImageIso p D L r

/-- The actual tensored normal kernel is the actual restriction of
the tensor of the negative normal twist with the same line. -/
def tensorKernelRestrictionIso (C : Y.IdealSheafData) :
    Scheme.Modules.tensorObj
      ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Divisors.negativeTwist D))) L ≅
      (Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj
          (Scheme.Modules.tensorObj (Stacks.Divisors.negativeTwist D) L)) :=
  CartierRestrictionTensor.tensorSumKernelIso D C L ≪≫
    (Scheme.Modules.pushforward C.subschemeι).mapIso
      (Stacks.RingedSpace.pullbackTensorIsoApp C.subschemeι.toLRSHom.toShHom
        (Stacks.Divisors.negativeTwist D) L).symm

/-- The genuine normal-kernel derived image is the genuine ordinary
image of the actual restricted normal tensor. -/
def derivedTensorKernelImageIso (C : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (rC : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (C.subschemeι ≫ p) rC] :
    derivedPushforwardModule p (Scheme.Modules.tensorObj
      ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Divisors.negativeTwist D))) L) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj
        ((Scheme.Modules.pushforward (C.subschemeι ≫ p)).obj
          ((Scheme.Modules.pullback C.subschemeι).obj
            (Scheme.Modules.tensorObj (Stacks.Divisors.negativeTwist D) L))) := by
  letI : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.negativeTwist D) := Stacks.Divisors.isInvertible_negativeTwist_picard D
  exact (derivedPushforward p.toLRSHom.toShHom).mapIso
    ((DerivedCategory.singleFunctor Y.Modules 0).mapIso
      (tensorKernelRestrictionIso D L C)) ≪≫
    derivedClosedImageIso p C (Scheme.Modules.tensorObj (Stacks.Divisors.negativeTwist D) L) rC

end M9Native.CartierRestrictionImages

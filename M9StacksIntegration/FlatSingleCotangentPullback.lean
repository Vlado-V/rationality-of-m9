module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt

/-!
# The literal deformation-theory single-pullback comparison for a flat sheaf

A flat sheaf in degree zero is K-flat. This proves invertibility of the
actual `derivedPullbackSingleObj` used by native morphism deformation
classes, retaining that literal comparison map. No flatness of the
underlying ringed-space morphism is required. Only already checked
native flat-single and comparison providers are used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open AlgebraicGeometry.RingedSpaceThickening

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.FlatSingleCotangentPullback

variable {X Y : RingedSpace.{u,u}} (g : X ⟶ Y)
variable (F : SheafOfModules.{u} (structureSheafRing Y))
variable (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u,u,u,u} (O := Y.sheaf) F)

include hF

/-- Actual flatness makes the literal native deformation comparison
invertible, for an arbitrary original ringed-space morphism. -/
theorem isIso_derivedPullbackSingleObj :
    IsIso (derivedPullbackSingleObj g F) := by
  have : IsIso ((derivedPullbackComparison g).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F))) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat g _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf F hF 0)
  dsimp only [derivedPullbackSingleObj]
  infer_instance

/-- A genuine isomorphism whose arrow is the exact original comparison. -/
def flatSingleIso :
    (derivedPullback g).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((modulePullback g).obj F) := by
  let := isIso_derivedPullbackSingleObj g F hF
  exact asIso (derivedPullbackSingleObj g F)

/-- No comparison arrow has been replaced in this isomorphism. -/
@[simp] theorem flatSingleIso_hom :
    (flatSingleIso g F hF).hom = derivedPullbackSingleObj g F := rfl

end M9Native.FlatSingleCotangentPullback

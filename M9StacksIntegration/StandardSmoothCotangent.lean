module

public import M9StacksIntegration.FlatSingleCotangentPullback
public import M9StacksIntegration.Private.DerivedHeartIso
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation

/-!
# Actual smooth cotangent normalization in the native morphism-class model

The original morphism-extension classes and their derived pullback use
the standard native derived model. Here the generic heart-comparison
construction is instantiated in exactly that model and normalized by
the original native H0(NL) comparison. Flatness of the actual smooth
cotangent then gives an actual derived pullback isomorphism. No model
identification, flatness of the map being deformed, or H0(df) equality is
supplied as an assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.StandardSmoothCotangent

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The actual original cotangent derived object used by native morphism classes. -/
abbrev nativeObject : DerivedCategory X.Modules :=
  relativeNaiveCotangentObj f.toLRSHom.toShHom

/-- Original standard-model H0(NL) is the original relative differentials. -/
def homologyZeroIso :
    (DerivedCategory.homologyFunctor X.Modules 0).obj (nativeObject f) ≅
      Scheme.Hom.relativeDifferentials f :=
  (DerivedCategory.homologyFunctorFactors X.Modules 0).app (Scheme.naiveCotangentComplex f) ≪≫
    Scheme.naiveCotangentComplexHomologyZeroIso f

theorem isGE_zero [Smooth f] : (nativeObject f).IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact (Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth f
    (Stacks.Smooth.formallySmoothScheme_of_smooth f) n (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules n).app (Scheme.naiveCotangentComplex f))

theorem isLE_zero [Smooth f] : (nativeObject f).IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  exact (Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth f
    (Stacks.Smooth.formallySmoothScheme_of_smooth f) n (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules n).app (Scheme.naiveCotangentComplex f))

/-- Genuine smooth normalization in the original standard morphism-class model. -/
def differentialsIso [Smooth f] :
    nativeObject f ≅ (DerivedCategory.singleFunctor X.Modules 0).obj
      (Scheme.Hom.relativeDifferentials f) := by
  let := isGE_zero f
  let := isLE_zero f
  exact DerivedHeartIso.toSingle _ _ (homologyZeroIso f)

/-- The normalization is exactly the original native H0 cotangent comparison. -/
theorem differentialsIso_homology [Smooth f] :
    (DerivedCategory.homologyFunctor X.Modules 0).map (differentialsIso f).hom ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app
        (Scheme.Hom.relativeDifferentials f)).hom = (homologyZeroIso f).hom := by
  let := isGE_zero f
  let := isLE_zero f
  exact DerivedHeartIso.H0_map_toSingle_hom _ _ (homologyZeroIso f)

/-- Actual smooth relative differentials are flat, from actual finite local freeness. -/
theorem differentials_isFlat [Smooth f] :
    SheafOfModules.IsFlat.{u,u,u,u} (O := X.sheaf) (Scheme.Hom.relativeDifferentials f) :=
  SheafOfModules.isFlat_of_isFiniteLocallyFree _
    (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f)

variable {Y : Scheme.{u}} (g : Y ⟶ X)

/-- Pulling back the actual original smooth cotangent complex gives the
actual pullback of its actual sheaf of differentials in degree zero. -/
def pulledDifferentialsIso [Smooth f] :
    (derivedPullback g.toLRSHom.toShHom).obj (nativeObject f) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj
        ((modulePullback g.toLRSHom.toShHom).obj (Scheme.Hom.relativeDifferentials f)) :=
  (derivedPullback g.toLRSHom.toShHom).mapIso (differentialsIso f) ≪≫
    FlatSingleCotangentPullback.flatSingleIso g.toLRSHom.toShHom
      (Scheme.Hom.relativeDifferentials f) (differentials_isFlat f)

/-- The exact comparison arrow is retained after the original smooth normalization. -/
theorem pulledDifferentialsIso_hom [Smooth f] :
    (pulledDifferentialsIso f g).hom =
      (derivedPullback g.toLRSHom.toShHom).map (differentialsIso f).hom ≫
        derivedPullbackSingleObj g.toLRSHom.toShHom (Scheme.Hom.relativeDifferentials f) := rfl

end M9Native.StandardSmoothCotangent

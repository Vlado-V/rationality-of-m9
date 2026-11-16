module

public import M9StacksIntegration.LagrangianConormalDeterminant
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr

/-!
# Actual pullback normalization of the original free-five conormal determinant

Exterior powers and native integer tensor powers are compared under the
original scheme-module pullback. The native ringed-space pullback is
related by its proved left-adjoint uniqueness isomorphism. Invertibility
of the pulled line is derived from invertibility of the original line.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant
open M9Native.LagrangianMatrixChart
open M9Native.LagrangianConormalDeterminant

universe u

namespace M9Native.LagrangianConormalDeterminantPullback

variable {X Y : Scheme.{u}}

/-- The original scheme-module pullback of an invertible line is genuinely invertible. -/
theorem pulledLine_isInvertible (i : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj L) :=
  Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj i L

/-- An actual line isomorphism induces an actual isomorphism of native integer powers. -/
def integerPowerCongr {L M : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (e : L ≅ M) (a : ℤ) :
    Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 M a := by
  letI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.presheaf X.ringCatSheaf.2 L
  letI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.presheaf X.ringCatSheaf.2 M
  exact Stacks.SheafOfModules.TensorPower.tensorPowerCongr X.presheaf X.ringCatSheaf.2 e a

/-- The genuine native integer-power pullback comparison at the original scheme functor. -/
def integerPullbackIso (i : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (a : ℤ) :
    letI := pulledLine_isInvertible i L
    (Scheme.Modules.pullback i).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) ≅
      Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback i).obj L) a := by
  letI := pulledLine_isInvertible i L
  letI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L) :=
    Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf i L
  let e := Stacks.ProjectiveBundleQuotients.pullbackIso i
  exact e.app (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) ≪≫
    Stacks.TensorPowerPullback.pullbackIntPowIso i.toLRSHom.toShHom L a ≪≫
      integerPowerCongr (e.app L).symm a

/-- Any actual exterior/integer-power identification pulls back to the literal exterior
of the original pulled sheaf, normalized in the literal pulled line. -/
def topExteriorPullbackOfIntegerIso (i : Y ⟶ X) (F : X.Modules) (r : ℕ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (a : ℤ)
    (d : topExterior F r ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) :
    letI := pulledLine_isInvertible i L
    topExterior ((Scheme.Modules.pullback i).obj F) r ≅
      Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback i).obj L) a :=
  (Scheme.Modules.exteriorPowerPullbackIso i F (r : ℤ)).symm ≪≫
    (Scheme.Modules.pullback i).mapIso d ≪≫ integerPullbackIso i L a

/-- The actual pullback of the literal free-five-first conormal model has exponent -5. -/
def pulledFreeFiveDualTopIso (i : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI := pulledLine_isInvertible i L
    topExterior ((Scheme.Modules.pullback i).obj (tensor (freeOn X 5) (dualSheaf L))) 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback i).obj L) (-5) :=
  topExteriorPullbackOfIntegerIso i (tensor (freeOn X 5) (dualSheaf L)) 5 L (-5)
    (freeFiveDualTopIso L)

end M9Native.LagrangianConormalDeterminantPullback

module

public import M9StacksIntegration.LagrangianConormalDeterminantPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomTensorIso
public import StacksFrontier.AlgebraicGeometry.Modules.DualFreeFinite

/-!
# The determinant of the actual dual five-equation bundle

The equation bundle is literally the line first and the native free sheaf
second. Native tensor--Hom currying and the actual finite free internal Hom
identify its dual with the free-first dual-line model. Thus the original
equation dual, and its original scheme pullback, have exponent minus five.
No tensor-dual comparison or determinant identification is supplied as data.
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
open M9Native.LagrangianConormalDeterminantPullback

universe u

namespace M9Native.LagrangianFiveEquationDeterminant

variable {X Y : Scheme.{u}}

/-- The actual dual of a line-first free tensor, computed by native currying
and the native internal Hom out of the literal finite free sheaf. -/
def dualLineFreeIso (L : X.Modules) (n : ℕ) :
    dualSheaf (tensor L (freeOn X n)) ≅ tensor (freeOn X n) (dualSheaf L) :=
  dualSheafIsoOfIso
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
        (freeOn X n) L) ≪≫
    Stacks.SheafOfModules.InternalHom.sheafInternalHomTensorIso X.sheaf
      (freeOn X n) L (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Stacks.AlgebraicGeometry.InternalHomLocalKernel.freeSheafInternalHomIso X.sheaf
      (dualSheaf L) (ULift.{u} (Fin n)) ≪≫
    Sigma.reindex (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)
      (fun _ : Fin n => dualSheaf L) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n => dualSheaf L)).symm ≪≫
    (freeTensorBiproductIso (dualSheaf L) n).symm

/-- The genuine top exterior of the original line-first five-equation dual. -/
def fiveEquationDualTopIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    topExterior (dualSheaf (tensor L (freeOn X 5))) 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-5) :=
  (Scheme.Modules.exteriorPowerFunctor X (5 : ℤ)).mapIso (dualLineFreeIso L 5) ≪≫
    freeFiveDualTopIso L

/-- The genuine exterior of the original pulled equation-dual bundle has
native exponent minus five in the original pulled determinant line. -/
def pulledFiveEquationDualTopIso (i : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI := pulledLine_isInvertible i L
    topExterior ((Scheme.Modules.pullback i).obj (dualSheaf (tensor L (freeOn X 5)))) 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback i).obj L) (-5) :=
  topExteriorPullbackOfIntegerIso i (dualSheaf (tensor L (freeOn X 5))) 5 L (-5)
    (fiveEquationDualTopIso L)

end M9Native.LagrangianFiveEquationDeterminant

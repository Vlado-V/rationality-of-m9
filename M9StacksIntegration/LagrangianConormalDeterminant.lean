module

public import M9StacksIntegration.LagrangianCurveAdjunction
public import M9StacksIntegration.LagrangianMatrixChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTensorFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial

/-!
# The actual free-five dual-line conormal determinant

The free module is the literal native free sheaf on ULift(Fin 5).
Tensoring its coproduct presentation with the actual dual line gives
an actual fivefold biproduct. Its top exterior is computed from native
split short exact sequences, then normalized to the native integer power.
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
open M9Native.SymmetricSquareIntegerTensorPower

universe u

namespace M9Native.LagrangianConormalDeterminant

variable {X : Scheme.{u}}

/-- Tensoring the literal original free module with a sheaf gives its actual finite biproduct. -/
def freeTensorBiproductIso (M : X.Modules) (n : ℕ) :
    tensor (freeOn X n) M ≅ (⨁ fun _ : Fin n => M) := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj M
  letI := Stacks.preservesColimitsOfSize_sheafTensorRight.{u,u,u,u} X.sheaf M
  let unitIso : T.obj (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 M
  exact PreservesCoproduct.iso T (fun _ : ULift.{u} (Fin n) =>
      SheafOfModules.unit X.ringCatSheaf) ≪≫
    Sigma.mapIso (fun _ : ULift.{u} (Fin n) => unitIso) ≪≫
    Sigma.reindex (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n) (fun _ : Fin n => M) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n => M)).symm

/-- The actual top exterior of repeated copies of a rank-one sheaf is its actual positive power. -/
def lineBiproductTopIso (M : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} M 1] :
    (m : ℕ) → topExterior (⨁ fun _ : Fin (m + 1) => M) (m + 1) ≅
      SheafOfModules.tensorPower (Opens.grothendieckTopology X) M (m + 1)
  | 0 => Scheme.Modules.exteriorPowerOneIsoSelf _ ≪≫ Scheme.Modules.biproductFinOneIso M
  | m + 1 => (Scheme.Modules.exteriorPowerBiproductSuccIso M m).symm ≪≫
      tensorIso (Iso.refl M) (lineBiproductTopIso M m)

/-- The top exterior of the literal free tensor, without a supplied frame or determinant isomorphism. -/
def freeLineTopIso (M : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} M 1] (m : ℕ) :
    topExterior (tensor (freeOn X (m + 1)) M) (m + 1) ≅
      SheafOfModules.tensorPower (Opens.grothendieckTopology X) M (m + 1) :=
  (Scheme.Modules.exteriorPowerFunctor X ((m + 1 : ℕ) : ℤ)).mapIso
    (freeTensorBiproductIso M (m + 1)) ≪≫ lineBiproductTopIso M m

/-- The actual free tensor with the actual dual of an invertible line has the native negative power. -/
def freeDualTopIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (m : ℕ) :
    topExterior (tensor (freeOn X (m + 1)) (dualSheaf L)) (m + 1) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L
        (-((m + 1 : ℕ) : ℤ)) := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf L) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf L 1 inferInstance
  exact freeLineTopIso (dualSheaf L) m ≪≫ positiveDualIsoNegative L (m + 1)

/-- The literal free-five-first conormal model has the genuine native exponent -5. -/
def freeFiveDualTopIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    topExterior (tensor (freeOn X 5) (dualSheaf L)) 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-5) :=
  freeDualTopIso L 4

end M9Native.LagrangianConormalDeterminant

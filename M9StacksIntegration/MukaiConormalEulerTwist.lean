module

public import M9StacksIntegration.MukaiConormalEulerPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! The actual determinant-twisted native conormal map to fourteen coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiConormalEulerTwist

open LagrangianGrassmannian LagrangianPluckerQuotient MukaiBundleDeterminant
open MukaiConormalEuler MukaiConormalEulerPairing

variable (K : Type u) [Field K] [CharZero K]

/-- Cancellation of each actual Euler O(-1) summand gives the actual
finite free fourteen-coordinate sheaf, not merely a rank equality. -/
def twistedMiddleIso : tensor (pulledMiddle K) (determinantLine K) ≅
    LagrangianMatrixChart.freeOn (space K) 14 := by
  let P := Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)
  let T := determinantTensorRight K
  let v : Fin 14 → (projectiveSpaceAtUniverse.{u} 13).Modules :=
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily (ULift.{u} ℤ) 13
  letI : T.IsEquivalence := determinantTensorRight_isEquivalence K
  letI : PreservesBiproduct (P.obj ∘ v) T := preservesBiproduct_of_preservesProduct T
  exact T.mapIso (P.mapBiproduct v) ≪≫
    T.mapBiproduct (P.obj ∘ v) ≪≫
    biproduct.mapIso (fun _ : Fin 14 => negativeDeterminantPairingIso K) ≪≫
    (Stacks.SheafOfModules.freeULiftFinIsoBiproduct (space K).sheaf 14).symm

/-- The genuine native map `N* tensor detQ → O^14`, obtained from the
original conormal differential and the actual Euler sequence. -/
def twistedConormalMap : MukaiConormalBundle.twistedConormal K ⟶
    LagrangianMatrixChart.freeOn (space K) 14 :=
  (determinantTensorRight K).map (conormalEulerMap K) ≫ (twistedMiddleIso K).hom

variable [IsAlgClosed K]

instance twistedConormalMap_mono : Mono (twistedConormalMap K) := by
  unfold twistedConormalMap
  infer_instance

end M9Native.MukaiConormalEulerTwist

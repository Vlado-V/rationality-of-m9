module

public import M9StacksIntegration.MukaiConormalEuler
public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible

/-!
# The canonical actual inverse-hyperplane determinant pairing

The inverse hyperplane factor in the Euler sequence is cancelled with
the actual universal quotient determinant by the proved O(1) pullback
isomorphism and native multiplication of twists. The pairing retains the original universal determinant line.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiConormalEulerPairing

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianPluckerGeneration
open MukaiBundleDeterminant MukaiConormalEuler

variable (K : Type u) [Field K] [CharZero K]

abbrev negativeLine : (space K).Modules :=
  (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).obj
    (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 14) (ULift.{u} ℤ)) (-1))

def negativeLineOverIso :
    (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).obj
        (twistOver 13 (Spec (.of K)) (-1)) ≅ negativeLine K :=
  (Scheme.Modules.pullbackComp (LagrangianPlucker.primitivePlucker K)
      (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))).app
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 14) (ULift.{u} ℤ)) (-1)) ≪≫
    (Scheme.Modules.pullbackCongr (LagrangianPlucker.primitivePlucker_toIntegral K)).app _

def basePairingIso :
    tensor (twistOver 13 (Spec (.of K)) (-1)) (twistOver 13 (Spec (.of K)) 1) ≅
      SheafOfModules.unit (projectiveSpaceOver 13 (Spec (.of K))).ringCatSheaf := by
  change Stacks.RelativeVeryAmple.tensorModules _ _ _ ≅ Stacks.Ample.unitModule _
  exact twistOverMulIso 13 (Spec (.of K)) (-1) 1 ≪≫
    eqToIso (congrArg (twistOver 13 (Spec (.of K))) (by norm_num : (-1 : ℤ) + 1 = 0)) ≪≫
      twistZeroIsoUnit 13 (Spec (.of K))

/-- The actual inverse Euler line pairs perfectly with the ORIGINAL
universal determinant, via its pinned native O(1) identification. -/
def negativeDeterminantPairingIso :
    tensor (negativeLine K) (determinantLine K) ≅
      SheafOfModules.unit (space K).ringCatSheaf :=
  tensorIso (negativeLineOverIso K).symm (determinantLineO1Iso K).symm ≪≫
    (Stacks.RingedSpace.pullbackTensorIsoApp
      (LagrangianPlucker.primitivePlucker K).toLRSHom.toShHom
      (twistOver 13 (Spec (.of K)) (-1)) (twistOver 13 (Spec (.of K)) 1)).symm ≪≫
    (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).mapIso
      (basePairingIso K) ≪≫
    Scheme.Modules.pullbackUnitIso (LagrangianPlucker.primitivePlucker K)

abbrev determinantTensorRight : (space K).Modules ⥤ (space K).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (space K).sheaf).flip.obj (determinantLine K)

instance determinantTensorRight_isEquivalence : (determinantTensorRight K).IsEquivalence := by
  let : SheafOfModules.IsInvertible (space K).sheaf.obj (space K).ringCatSheaf.property
      (determinantLine K) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ (determinantLine_invertible K)
  exact Scheme.Modules.isEquivalence_invertibleTensorRightFunctor (determinantLine K)

end M9Native.MukaiConormalEulerPairing

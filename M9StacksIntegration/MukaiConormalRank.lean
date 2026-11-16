module

public import M9StacksIntegration.MukaiConormalEulerTwist
public import M9StacksIntegration.LagrangianConormalRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral

/-!
# Actual rank seven of the native determinant-twisted conormal

The actual pulled Euler sequence gives rank thirteen for the twisted
ambient cotangent sheaf. The actual conormal sequence and the independently
proved native cotangent rank six then give rank seven for the original
conormal twist. Neither ambient cotangent rank nor conormal rank is input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiConormalRank

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open MukaiBundleDeterminant MukaiConormalCotangentTransport MukaiConormalEuler
open MukaiConormalEulerPairing MukaiConormalEulerTwist

theorem shortExact_first_rank {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (a c : ℕ)
    (h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ a)
    (h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ c) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ (a-c) := by
  let : Mono S.f := hS.mono_f
  have hk := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    S.g hS.epi_g a c h₂ h₃
  let e : S.X₁ ≅ kernel S.g :=
    hS.exact.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm hk

variable (K : Type u) [Field K] [CharZero K]

def ambientIntegralIso : (MukaiConormalSequence.sequence K).X₂ ≅
    (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).obj
      (Scheme.Hom.relativeDifferentials (integralProjection 13)) :=
  ((Scheme.Modules.pullbackComp (LagrangianPlucker.primitivePlucker K)
    (LagrangianPluckerLinear.primitiveProjectiveIso K).hom).app
      (Scheme.Hom.relativeDifferentials (MukaiConormalSequence.ambientProjection K))).symm ≪≫
  (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).mapIso
    (ambientCoordinateCotangentIso K) ≪≫
  (Scheme.Modules.pullback (LagrangianPlucker.primitivePlucker K)).mapIso
    (projectiveCotangentBaseChangeIso 13 (Spec (.of K))).symm ≪≫
  (Scheme.Modules.pullbackComp (LagrangianPlucker.primitivePlucker K)
    (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))).app
      (Scheme.Hom.relativeDifferentials (integralProjection 13)) ≪≫
  (Scheme.Modules.pullbackCongr (LagrangianPlucker.primitivePlucker_toIntegral K)).app
    (Scheme.Hom.relativeDifferentials (integralProjection 13))

def twistedEulerSequence : ShortComplex (space K).Modules :=
  ((integralSequence.map
    (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K))).map
      (determinantTensorRight K))

theorem twistedEulerSequence_shortExact : (twistedEulerSequence K).ShortExact := by
  let T := determinantTensorRight K
  let : T.IsEquivalence := determinantTensorRight_isEquivalence K
  exact (pulledIntegralSequence_shortExact K).map_of_exact T

theorem twistedAmbient_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (tensor (MukaiConormalSequence.sequence K).X₂ (determinantLine K)) 13 := by
  let P := Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)
  let T := determinantTensorRight K
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistedEulerSequence K).X₂ 14 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (twistedMiddleIso K).symm
      (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := (space K).ringCatSheaf) 14)
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistedEulerSequence K).X₃ 1 := by
    let := SheafOfModules.isFiniteLocallyFreeOfRank_unit (projectiveSpaceAtUniverse.{u} 13)
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (P.obj (SheafOfModules.unit (projectiveSpaceAtUniverse.{u} 13).ringCatSheaf)) 1 :=
      isFiniteLocallyFreeOfRank_pullback _ _ 1
    exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (space K)
      (P.obj (SheafOfModules.unit (projectiveSpaceAtUniverse.{u} 13).ringCatSheaf))
      (determinantLine K) 1 1
  have h₁ := shortExact_first_rank (twistedEulerSequence K)
    (twistedEulerSequence_shortExact K) 14 1 h₂ h₃
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (T.mapIso (ambientIntegralIso K)).symm h₁

variable [IsAlgClosed K]

def twistedConormalSequence : ShortComplex (space K).Modules :=
  (MukaiConormalSequence.sequence K).map (determinantTensorRight K)

theorem twistedConormalSequence_shortExact : (twistedConormalSequence K).ShortExact := by
  let T := determinantTensorRight K
  let : T.IsEquivalence := determinantTensorRight_isEquivalence K
  exact (MukaiConormalSequence.sequence_shortExact K).map_of_exact T

theorem twistedConormal_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (MukaiConormalBundle.twistedConormal K) 7 := by
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (twistedConormalSequence K).X₃ 6 := by
    let := LagrangianDegree.lagrangianDifferentials_rank K
    exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (space K)
      (Scheme.Hom.relativeDifferentials (projection K)) (determinantLine K) 6 1
  exact shortExact_first_rank (twistedConormalSequence K)
    (twistedConormalSequence_shortExact K) 13 6 (twistedAmbient_rank K) h₃

end M9Native.MukaiConormalRank

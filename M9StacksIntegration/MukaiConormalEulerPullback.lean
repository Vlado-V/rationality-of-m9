module

public import M9StacksIntegration.MukaiConormalRank
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackLocallySplit

/-!
# Pullback injectivity of the actual twisted conormal Euler map

The two actual short exact sequences have finite locally free quotients
of ranks one and six.  Their local splittings preserve both inclusions
under arbitrary pullback.  The actual twisted conormal map is their
composite through the pinned ambient-cotangent and Euler coordinate isomorphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace M9Native.MukaiConormalEulerPullback

open LagrangianGrassmannian LagrangianPluckerQuotient MukaiBundleDeterminant
open MukaiConormalEuler MukaiConormalCotangentTransport MukaiConormalEulerPairing
open MukaiConormalEulerTwist MukaiConormalRank

variable (K : Type u) [Field K] [CharZero K]

theorem twistedEuler_quotient_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistedEulerSequence K).X₃ 1 := by
  let P := Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)
  let := SheafOfModules.isFiniteLocallyFreeOfRank_unit (projectiveSpaceAtUniverse.{u} 13)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (P.obj (SheafOfModules.unit (projectiveSpaceAtUniverse.{u} 13).ringCatSheaf)) 1 :=
    isFiniteLocallyFreeOfRank_pullback _ _ 1
  exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (space K)
    (P.obj (SheafOfModules.unit (projectiveSpaceAtUniverse.{u} 13).ringCatSheaf))
    (determinantLine K) 1 1

theorem conormalToIntegralCotangent_factor :
    conormalToIntegralCotangent K = MukaiConormalSequence.inclusion K ≫
      (ambientIntegralIso K).hom := by
  simp only [conormalToIntegralCotangent, conormalToFieldCotangent, ambientIntegralIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]

/-- The factorization uses the two actual inclusions, not their abstract ranks. -/
theorem twistedConormalMap_factor :
    twistedConormalMap K =
      (determinantTensorRight K).map (MukaiConormalSequence.inclusion K) ≫
        (determinantTensorRight K).map (ambientIntegralIso K).hom ≫
          (twistedEulerSequence K).f ≫ (twistedMiddleIso K).hom := by
  simp only [twistedConormalMap, conormalEulerMap, conormalToIntegralCotangent_factor,
    Functor.map_comp, twistedEulerSequence, ShortComplex.map_f, integralSequence, Category.assoc]

theorem pullback_twistedEuler_shortExact {T : Scheme.{u}} (g : T ⟶ space K) :
    ((twistedEulerSequence K).map (Scheme.Modules.pullback g)).ShortExact := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (twistedEulerSequence K).X₃ :=
    (twistedEuler_quotient_rank K).isFiniteLocallyFree
  exact Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree g _
    (twistedEulerSequence_shortExact K)

variable [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem twistedConormal_quotient_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistedConormalSequence K).X₃ 6 := by
  let := LagrangianDegree.lagrangianDifferentials_rank K
  exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (space K)
    (Scheme.Hom.relativeDifferentials (projection K)) (determinantLine K) 6 1

theorem pullback_twistedConormal_shortExact {T : Scheme.{u}} (g : T ⟶ space K) :
    ((twistedConormalSequence K).map (Scheme.Modules.pullback g)).ShortExact := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (twistedConormalSequence K).X₃ :=
    (twistedConormal_quotient_rank K).isFiniteLocallyFree
  exact Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree g _
    (twistedConormalSequence_shortExact K)

/-- Arbitrary base change preserves the original twisted conormal Euler
inclusion, by the actual local splittings of its two actual quotient sequences. -/
theorem pullback_twistedConormalMap_mono {T : Scheme.{u}} (g : T ⟶ space K) :
    Mono ((Scheme.Modules.pullback g).map (twistedConormalMap K)) := by
  let : Mono ((Scheme.Modules.pullback g).map
      ((determinantTensorRight K).map (MukaiConormalSequence.inclusion K))) :=
    (pullback_twistedConormal_shortExact K g).mono_f
  let : Mono ((Scheme.Modules.pullback g).map (twistedEulerSequence K).f) :=
    (pullback_twistedEuler_shortExact K g).mono_f
  rw [twistedConormalMap_factor, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

end M9Native.MukaiConormalEulerPullback

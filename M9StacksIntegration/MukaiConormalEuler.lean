module

public import M9StacksIntegration.MukaiConormalCotangentTransport
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackLocallySplit

/-!
# The actual native conormal-to-Euler map

The source is the original categorical conormal sheaf of the proved
primitive Plücker closed immersion. The target is the actual pullback of
the fourteen native O(-1) summands of the literal integral Euler sequence.
No first-jet-kernel identification or symmetric-square projection is
supplied as a definition or hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.MukaiConormalEuler

open MukaiConormalCotangentTransport

abbrev integralMiddle : (projectiveSpaceAtUniverse.{u} 13).Modules :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum (ULift.{u} ℤ) 13

def integralEulerFirst : Scheme.Hom.relativeDifferentials (integralProjection 13) ⟶
    integralMiddle.{u} :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.eulerFirstArrow (ULift.{u} ℤ) 13

def integralEulerLast : integralMiddle.{u} ⟶
    SheafOfModules.unit (projectiveSpaceAtUniverse.{u} 13).ringCatSheaf :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.eulerSurjection (ULift.{u} ℤ) 13

theorem integralEuler_comp : integralEulerFirst.{u} ≫ integralEulerLast = 0 :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.eulerFirstArrow_comp_eulerSurjection
    (ULift.{u} ℤ) 13

def integralSequence : ShortComplex (projectiveSpaceAtUniverse.{u} 13).Modules :=
  ShortComplex.mk integralEulerFirst integralEulerLast integralEuler_comp

theorem integralSequence_shortExact : integralSequence.{u}.ShortExact :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_eulerSequence (ULift.{u} ℤ) 13

variable (K : Type u) [Field K] [CharZero K]

abbrev pulledMiddle : (LagrangianGrassmannian.space K).Modules :=
  (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).obj integralMiddle

/-- The actual original conormal differential followed by the actual
native Euler inclusion; this is a constructed sheaf morphism. -/
def conormalEulerMap : MukaiConormalBundle.conormal K ⟶ pulledMiddle K :=
  conormalToIntegralCotangent K ≫
    (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).map integralEulerFirst

theorem conormalEulerMap_comp_last :
    conormalEulerMap K ≫
      (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K)).map
        integralEulerLast = 0 := by
  simp only [conormalEulerMap, Category.assoc, ← Functor.map_comp, integralEuler_comp,
    Functor.map_zero, comp_zero]

theorem pulledIntegralSequence_shortExact :
    (integralSequence.map
      (Scheme.Modules.pullback (LagrangianPlucker.integralPrimitivePlucker K))).ShortExact := by
  let := SheafOfModules.isFiniteLocallyFreeOfRank_unit (projectiveSpaceAtUniverse.{u} 13)
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} integralSequence.X₃ := by
    change SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (SheafOfModules.unit (projectiveSpaceAtUniverse.{u} 13).ringCatSheaf)
    infer_instance
  exact Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree _ _
    integralSequence_shortExact

variable [IsAlgClosed K]

instance conormalEulerMap_mono : Mono (conormalEulerMap K) := by
  have : Mono ((Scheme.Modules.pullback
      (LagrangianPlucker.integralPrimitivePlucker K)).map integralEulerFirst) :=
    (pulledIntegralSequence_shortExact K).mono_f
  unfold conormalEulerMap
  infer_instance

end M9Native.MukaiConormalEuler

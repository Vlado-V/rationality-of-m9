module

public import M9StacksIntegration.LagrangianFiveSectionModel
public import M9StacksIntegration.CurveConstantRankFibers
public import M9StacksIntegration.MukaiShortExactFiberRank

/-!
# Actual fibre injectivity for a transverse original LG five-section

The zero scheme is the literal native zero scheme of the determinant-line
tensor free-five section. Actual smooth relative dimension one supplies
the genuine equation conormal sequence. Its quotient is the actual curve
cotangent line, so flatness proves injectivity on every residue fibre.
No conormal injection, equation-rank, or transversality-model premise is
supplied as an additional hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianTransverseConormalFiber

open LagrangianFiveSectionModel

variable (K : Type u) [Field K]
  (s : Γ(equationBundle K, ⊤))
  [SmoothOfRelativeDimension 1 (structureMap K s)]

/-- Genuine smooth curve geometry makes the original equation map injective
on every original residue-field fibre. -/
theorem equationMap_fiber_injective (x : curve K s) :
    Function.Injective
      (MukaiSemiIrreducible.fiberMap (conormalSequence K s).f x) := by
  exact CurveConstantRankFibers.fiberMap_injective_of_shortExact
    (conormalSequence K s) (conormalSequence_shortExact K s)
    (curveDifferentials_rank K s).isFiniteLocallyFree x

/-- Thus every actual nonzero equation-cotangent fibre vector has nonzero actual differential. -/
theorem equationMap_fiber_ne_zero (x : curve K s)
    (v : MukaiSemiIrreducible.Fiber (conormalSequence K s).X₁ x) (hv : v ≠ 0) :
    MukaiSemiIrreducible.fiberMap (conormalSequence K s).f x v ≠ 0 := by
  intro h
  apply hv
  exact equationMap_fiber_injective K s x (h.trans (map_zero _).symm)

/-- The genuine original equation conormal map has rank five at every original point. -/
theorem equationMap_everywhereRank :
    MukaiSemiIrreducible.EverywhereRank (conormalSequence K s).f 5 := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalSequence K s).X₂ 6 :=
    LagrangianCurveConormal.middle_rank K (inclusion K s)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalSequence K s).X₃ 1 :=
    curveDifferentials_rank K s
  have h := MukaiShortExactFiberRank.everywhereRank_comp
    (conormalSequence K s) (conormalSequence_shortExact K s) 6 1 (𝟙 _)
  simpa only [Category.id_comp] using h

end M9Native.LagrangianTransverseConormalFiber

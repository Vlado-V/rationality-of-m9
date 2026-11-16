module

public import M9StacksIntegration.DirectC9InitialFree
public import M9StacksIntegration.ChowFreeLineTensor
public import M9StacksIntegration.DirectC9GraphRootEvaluation

/-! The actual initial C9 direct image has the true nine-normalization
line Chern family, by its constructed free-first tensor isomorphism.
There is no Chern, triviality or K-zero input premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u

namespace M9Native.DirectC9InitialChern

open Stacks.Chow Stacks.Chow.GenuineChern DirectC9GraphRootEvaluation GradedLineCapSubring

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)

include hg

theorem initial_chernFamily (A : ChowSituation.{u})
    (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s] :
    @chernFamily A (power C 9).left s _ (DirectC9Bundles.movingPushforward k C c₀ 0 (Nat.zero_le 9)) 9
      (by simpa only [Nat.add_zero] using
        DirectC9Bundles.movingPushforward_rank k C c₀ hg 0 (Nat.zero_le 9)) =
      (1 + lineFamily A s (normalizationLine C c₀)) ^ 9 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (DirectC9Bundles.movingPushforward k C c₀ 0 (Nat.zero_le 9)) 9 := by
    simpa only [Nat.add_zero] using DirectC9Bundles.movingPushforward_rank k C c₀ hg 0 (Nat.zero_le 9)
  exact ChowFreeLineTensor.chernFamily_of_iso_freeTensor A s
    (DirectC9Bundles.movingPushforward k C c₀ 0 (Nat.zero_le 9))
    (normalizationLine C c₀) 9 (DirectC9InitialFree.initialIso k C c₀ hg)

end M9Native.DirectC9InitialChern

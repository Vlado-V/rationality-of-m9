module

public import M9StacksIntegration.ChowFlagThreeInputs
public import M9StacksIntegration.ChowThirdTensorGysin

/-!
# Actual original flag classes under the three genuine Gysin maps

The comparison here concerns the original native projective maps and
their actual normalized input class. It uses only genuine degree casts
and the proved equality of original structure morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.ChowFlagThreeGysin
open ChowFlagThreeStages ChowFlagThreeInputs ChowProjectiveTensorInput
open ChowTensorGysinComposition ChowThirdTensorGysin

section Cast
variable (C : ChowSituation.{u}) {Y : Scheme.{u}}

/-- The displayed change of the same original structure morphism has
the inverse change as its actual inverse on Chow classes. -/
theorem structureMapCast_back (f g : Y ⟶ C.S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f=g) (k : ℤ)
    (β : chowGroup C f k) :
    structureMapCast C g f h.symm k (structureMapCast C f g h k β) = β := by
  subst g
  rfl

theorem structureMapCast_zero (f g : Y ⟶ C.S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f=g) (k : ℤ) :
    structureMapCast C f g h k (0 : chowGroup C f k) = 0 := by
  subst g
  rfl

end Cast

variable {X : Scheme.{u}} (D F : X.Modules)
    [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 10]
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
  hD.isFiniteLocallyFree
local instance originalProjectionLFT : LocallyOfFiniteType (FlagThreeQuotient.projection D) :=
  ChowFlagThreeStages.originalProjectionLFT D

/-- Three literal proper pushforwards of the actual normalized class. -/
def normalTensorPush (k : ℤ) (α : chowGroup C q k) : chowGroup C q (k-9) :=
  triplePush D C q (k-9) (normalTensorInput D F C q k α)

/-- The class-level actual projective pushes are exactly the three
geometric tensor Gysin operations. No trace comparison is supplied. -/
theorem normalTensorPush_eq_tripleTensorPush (k : ℤ) (α : chowGroup C q k) :
    normalTensorPush D F C q k α = tripleTensorPush D F C q k α := by
  dsimp only [normalTensorPush, triplePush, AddMonoidHom.comp_apply,
    normalTensorInput, middleTensorInput, outerTensorInput,
    tripleTensorPush, doubleTensorPush, push1, push2, push3,
    ]
  simp only [ChowProjectiveTensorPushTerms.properPush_cast,
    ChowProjectiveTensorInput.push_tensorInput,
    chowGroupCast_chowGroupCast]

/-- The same three actual maps, with the input written on the literal
original native flag structure morphism. -/
def pushOnOriginalFlag (l : ℤ)
    (β : chowGroup C (FlagThreeQuotient.projection D ≫ q) l) : chowGroup C q l :=
  triplePush D C q l
    (structureMapCast C (FlagThreeQuotient.projection D ≫ q) (baseMap3 D C q)
      (baseMap3_eq_original D C q).symm l β)

theorem pushOnOriginalFlag_zero (l : ℤ) :
    pushOnOriginalFlag D C q l 0 = 0 := by
  rw [pushOnOriginalFlag, structureMapCast_zero, map_zero]

theorem push_original_normalTensorInput (k : ℤ) (α : chowGroup C q k) :
    pushOnOriginalFlag D C q (k-9) (normalTensorInputOnOriginalFlag D F C q k α) =
      tripleTensorPush D F C q k α := by
  rw [pushOnOriginalFlag, normalTensorInputOnOriginalFlag, structureMapCast_back]
  exact normalTensorPush_eq_tripleTensorPush D F C q k α

/-- The three genuine actual pushes of the original normalized class
give the ordered six coefficient words. -/
theorem push_original_normalTensorInput_eq_orderedWords (k : ℤ) (α : chowGroup C q k) :
    pushOnOriginalFlag D C q (k-9) (normalTensorInputOnOriginalFlag D F C q k α) =
      orderedWords C q (ChowSignedVirtualFamily.family C q F D 10 10) k 9 α := by
  rw [push_original_normalTensorInput, tripleTensorPush_eq_orderedWords]

end M9Native.ChowFlagThreeGysin

namespace M9Native.ChowFlagThreeGysin

open Stacks.AlgebraicGeometry.ReflexiveModules GradedCapVirtualSchur

/-- On the original dual source, the actual normalized flag class is
pushed to the actual ordinary virtual Schur component. -/
theorem push_original_normalTensorInput_dual_eq_schur {X : Scheme.{u}}
    (E F : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 10]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q] :
    letI := isFiniteLocallyFreeOfRank_dualSheaf E 10 hE
    ∀ (k : ℤ) (α : chowGroup C q k),
      pushOnOriginalFlag (dualSheaf E) C q (k-9)
          (ChowFlagThreeInputs.normalTensorInputOnOriginalFlag
            (dualSheaf E) F C q k α) =
        schur333 (virtualFamily C q F E 10 10) k 9 α := by
  letI := isFiniteLocallyFreeOfRank_dualSheaf E 10 hE
  intro k α
  exact (push_original_normalTensorInput (dualSheaf E) F C q k α).trans
    (ChowThirdTensorGysin.tripleTensorPush_dual_eq_schur E F C q k α)

end M9Native.ChowFlagThreeGysin

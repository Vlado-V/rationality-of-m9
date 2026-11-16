module

public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeReflexive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations

/-!
# Actual dual-span and extension determinants

These computations use the genuine dual evaluation and extension short exact
sequences. This small leaf isolates them from the separate degree and canonical
bundle theorems. It constructs the determinant identifications; none is supplied
as an assumption. The full staged determinant/degree source remains unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
universe u
namespace M9Native.MukaiDualSpanDeterminant
variable {X : Scheme.{u}}

/-- The rank-two dual span has top exterior power β, calculated from
the actual dual evaluation short exact sequence. -/
def dualSpanTopExteriorIso (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s)) :
    topExterior (dualSpan β s) 2 ≅ β := by
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree β 1
  letI := isFiniteLocallyFreeOfRank_dualSheaf β 1 inferInstance
  letI := dualSpan_rank β s hgen
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank
      (dualSheaf (evaluationKernel β s)) (1 + 1) := dualSpan_rank β s hgen
  let w := Classical.choose (dualEvaluationSequence_shortExact β s hgen)
  have hS := Classical.choose_spec (dualEvaluationSequence_shortExact β s hgen)
  let htop : tensor (dualSheaf β) (topExterior (dualSpan β s) 2) ≅ structureModule X :=
    tensorIso (Scheme.Modules.exteriorPowerOneIsoSelf (dualSheaf β)).symm
        (Iso.refl _) ≪≫
      Scheme.Modules.exteriorPowerTensorExteriorPowerIso
        (dualMap (netEvaluation β s)) (dualMap (evaluationKernelInclusion β s)) w hS 1 1 ≪≫
      freeTopExteriorIso 3 (dualSheaf (netFree X)) (dualNetFreeIso X)
  let hdual : topExterior (dualSpan β s) 2 ≅ dualSheaf (dualSheaf β) :=
    tensorInverseNativeIso (dualSheaf β) (topExterior (dualSpan β s) 2) htop
  letI := isIso_toDoubleDual_of_isFiniteLocallyFree β
  exact hdual ≪≫ (asIso (toDoubleDual β)).symm

/-- Both actual rank-two top exterior powers tensor to the original residual
line-bundle tensor, without a supplied determinant relation. -/
def dualSpansTopExteriorTensorIso (α β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (sα : ULift.{u} (Fin 3) → α.sections) (hα : Epi (netEvaluation α sα))
    (sβ : ULift.{u} (Fin 3) → β.sections) (hβ : Epi (netEvaluation β sβ)) :
    tensor (topExterior (dualSpan α sα) 2) (topExterior (dualSpan β sβ) 2) ≅ tensor α β :=
  tensorIso (dualSpanTopExteriorIso α sα hα) (dualSpanTopExteriorIso β sβ hβ)

/-- The actual top exterior power of an extension of α by Qβ is α⊗β. -/
def extensionTopExteriorIso (β α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    {E : X.Modules} (i : dualSpan β s ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact) : topExterior E 3 ≅ tensor α β := by
  letI := dualSpan_rank β s hgen
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α
  exact (Scheme.Modules.exteriorPowerTensorExteriorPowerIso i p w hS 2 0).symm ≪≫
    tensorIso (dualSpanTopExteriorIso β s hgen)
      (Scheme.Modules.exteriorPowerOneIsoSelf α) ≪≫
    Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace β α

/-- The actual top exterior power of an extension by the literal residual line
is the original line ω, by the constructed tensor cancellation. -/
def literalResidualExtensionTopExteriorIso (ω α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (s : ULift.{u} (Fin 3) → (residualLine ω α).sections)
    (hgen : Epi (netEvaluation (residualLine ω α) s))
    {E : X.Modules} (i : dualSpan (residualLine ω α) s ⟶ E) (p : E ⟶ α)
    (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact) :
    topExterior E 3 ≅ ω := by
  letI := residualLine_isInvertible ω α
  exact extensionTopExteriorIso (residualLine ω α) α s hgen i p w hS ≪≫
    residualTensorIso ω α

end M9Native.MukaiDualSpanDeterminant

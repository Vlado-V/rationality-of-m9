module

public import M9StacksIntegration.MukaiDualSpanDeterminant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant

/-! The actual Tag 0FJN annihilator determinant layer, using the native
proved identification with the top exterior power. -/
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
universe u
namespace M9Native.MukaiDualSpanDeterminant
variable {X : Scheme.{u}}

/-- The actual annihilator determinant of the constructed dual span is
β; no determinant equality was supplied as bundle data. -/
def dualSpanDeterminantIso (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s)) :
    Scheme.Modules.determinant (dualSpan β s) ≅ β := by
  letI := dualSpan_rank β s hgen
  exact (Scheme.Modules.exteriorPowerIsoDeterminant (dualSpan β s) 2).symm ≪≫
    dualSpanTopExteriorIso β s hgen

/-- The determinant tensor of the two actual dual-span bundles is the
tensor of the two original line bundles. This is the determinant input to
Mukai's rank-two parity argument, derived from the evaluation sequences. -/
def dualSpansDeterminantTensorIso (α β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (sα : ULift.{u} (Fin 3) → α.sections) (hα : Epi (netEvaluation α sα))
    (sβ : ULift.{u} (Fin 3) → β.sections) (hβ : Epi (netEvaluation β sβ)) :
    tensor (Scheme.Modules.determinant (dualSpan α sα))
      (Scheme.Modules.determinant (dualSpan β sβ)) ≅ tensor α β :=
  tensorIso (dualSpanDeterminantIso α sα hα) (dualSpanDeterminantIso β sβ hβ)



/-- The determinant of the actual rank-three extension is α⊗β, with
the middle rank obtained from the actual short exact sequence. -/
def extensionDeterminantIso (β α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    {E : X.Modules} (i : dualSpan β s ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact) :
    Scheme.Modules.determinant E ≅ tensor α β := by
  letI := extension_rank (ShortComplex.mk i p w) hS 2 1
    (dualSpan_rank β s hgen)
    (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α)
  exact (Scheme.Modules.exteriorPowerIsoDeterminant E 3).symm ≪≫
    extensionTopExteriorIso β α s hgen i p w hS


/-- With β defined literally as `ω ⊗ αᵛ`, the determinant relation
is proved without a supplied residual isomorphism. -/
def literalResidualExtensionDeterminantIso (ω α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (s : ULift.{u} (Fin 3) → (residualLine ω α).sections)
    (hgen : Epi (netEvaluation (residualLine ω α) s))
    {E : X.Modules} (i : dualSpan (residualLine ω α) s ⟶ E) (p : E ⟶ α)
    (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact) :
    Scheme.Modules.determinant E ≅ ω := by
  letI := residualLine_isInvertible ω α
  exact extensionDeterminantIso (residualLine ω α) α s hgen i p w hS ≪≫
    residualTensorIso ω α



end M9Native.MukaiDualSpanDeterminant

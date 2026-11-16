module

public import M9StacksIntegration.LagrangianIncidenceFourCutBase
public import M9StacksIntegration.LagrangianPluckerClosed
public import M9StacksIntegration.ChowLineProperCapPower
public import M9StacksIntegration.LineFamilyCapPower

/-! The actual incidence projection preserves four caps of its literal
pulled-back determinant line. This is genuine native proper-push
naturality on every actual degree-four class, without a compatibility,
class, smoothness, or numerical premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern
universe u
namespace M9Native.LagrangianIncidenceFourCapPush
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianIncidenceFourCutBase
open ChowCapWords GradedLineCapSubring
variable (K : Type u) [Field K] [CharZero K]

abbrev structuralMap (w : Fin 2 → (Fin 6 → K)) :=
  LagrangianArbitraryPlaneIncidence.incidenceToLG K w ≫ projection K

instance structuralMap_proper (w : Fin 2 → (Fin 6 → K)) :
    IsProper (structuralMap K w) := by
  let : IsProper (projection K) := isProper_of_isProjectiveMorphism _
    (LagrangianPluckerClosed.isProjectiveMorphism_projection K)
  dsimp [structuralMap]
  infer_instance

/-- The original proper projection carries the SAME four line caps
to the original four Plucker caps, on every actual degree-four class. -/
theorem fourCap_push (w : Fin 2 → (Fin 6 → K))
    (α : chowGroup (fieldChowSituation K) (structuralMap K w) 4) :
    ChowLineProperPush.properPush (fieldChowSituation K) (structuralMap K w)
      (projection K) (LagrangianArbitraryPlaneIncidence.incidenceToLG K w) rfl 0
      (capPow (fieldChowSituation K) (structuralMap K w)
        (lineCap (fieldChowSituation K) (structuralMap K w) (invertibleLine K w))
        4 4 0 (by omega) α) =
      capPow (fieldChowSituation K) (projection K)
        (lineCap (fieldChowSituation K) (projection K)
          ⟨determinantLine K,determinantLine_invertible K⟩) 4 4 0 (by omega)
        (ChowLineProperPush.properPush (fieldChowSituation K) (structuralMap K w)
          (projection K) (LagrangianArbitraryPlaneIncidence.incidenceToLG K w) rfl 4 α) := by
  exact ChowLineProperCapPower.properPush_capPow (fieldChowSituation K)
    (structuralMap K w) (projection K) (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
    rfl ⟨determinantLine K,determinantLine_invertible K⟩ (invertibleLine K w)
    (Iso.refl _) 4 4 0 (by omega) α

end M9Native.LagrangianIncidenceFourCapPush

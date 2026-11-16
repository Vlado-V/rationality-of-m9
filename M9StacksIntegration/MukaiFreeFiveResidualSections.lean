module

public import M9StacksIntegration.MukaiBasepointFreePencilTrick
public import M9StacksIntegration.CanonicalPencilBounds
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree

/-!
# Actual residual section counts in the free degree-five pencil case

The pencil trick for a genuinely generating pair, actual line degrees,
native Riemann--Roch and native Serre duality bound both degree-eight
canonical residual lines by three sections. No completeness of the
original six-section system, containment of the pencil in its image,
absence of degree-five pencils, or Hom-vanishing is used.

The basepointed degree-five case whose moving part has degree four is
not asserted by these statements.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiFreeFiveResidualSections

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsProper f]
  (hdim : topologicalKrullDim X ≤ 1)

/-- The native residual has the actual difference of the original line degrees. -/
theorem residual_degree (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] :
    let := residualLine_isInvertible A B
    invertibleCurveDegree K f hdim (residualLine A B) =
      invertibleCurveDegree K f hdim A - invertibleCurveDegree K f hdim B := by
  let := residualLine_isInvertible A B
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensor B (residualLine A B)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible
      X.presheaf X.ringCatSheaf.2 B (residualLine A B)
  have hp := invertibleCurveDegree_tensorSheaf_eq_add K f hdim B (residualLine A B)
  change invertibleCurveDegree K f hdim (tensor B (residualLine A B)) =
    invertibleCurveDegree K f hdim B +
      invertibleCurveDegree K f hdim (residualLine A B) at hp
  have he := invertibleCurveDegree_eq_of_iso K f hdim (residualTensorIso A B)
  omega

omit [IsProper f] in
/-- The original field-linear Hom is the original residual line's H0. -/
theorem hom_finrank_eq_residual_h0 (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] :
    let := modulesLinearOverField K f
    Module.finrank K (B ⟶ A) =
      Module.finrank K (cohomologyOverField K f (residualLine A B) 0) := by
  let := modulesLinearOverField K f
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X B
  let := isFiniteLocallyFreeOfRank_dualSheaf B 1 inferInstance
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} B :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree B 1
  let : IsIso (toDoubleDual B) := isIso_toDoubleDual_of_isFiniteLocallyFree B
  exact ((Linear.homCongr K (asIso (toDoubleDual B)) (Iso.refl A)).trans
    ((MukaiRecognitionHomBound.homDualTensorH0Equiv K f (dualSheaf B) A 1).trans
      (cohomologyOverFieldIso K f
        (MukaiTensorLineCancellation.tensorSwap (dualSheaf B) A) 0).toLinearEquiv)).finrank_eq

variable [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]

/-- The other actual residual degree is eight, derived from the actual canonical line. -/
theorem other_degree_eight (hg : genus f = 9) (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    (e : tensor A B ≅ Stacks.Duality.dualizingSheafOverField f)
    (hB : invertibleCurveDegree K f hdim B = 8) :
    invertibleCurveDegree K f hdim A = 8 := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tensor A B) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible
      X.presheaf X.ringCatSheaf.2 A B
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) :=
    Stacks.SheafOfModules.isInvertible_of_iso X.presheaf X.ringCatSheaf.2 e
  have hp := invertibleCurveDegree_tensorSheaf_eq_add K f hdim A B
  change invertibleCurveDegree K f hdim (tensor A B) =
    invertibleCurveDegree K f hdim A + invertibleCurveDegree K f hdim B at hp
  have he := invertibleCurveDegree_eq_of_iso K f hdim e
  have hw := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible K f hdim
  rw [hg] at hw
  omega

/-- A genuine free degree-five pencil bounds the actual degree-eight line's H0.
The complete pencil dimension and Hom-vanishing are not inputs. -/
theorem h0_le_three (hg : genus f = 9)
    (hno3 : ¬ Nonempty (LinearSeries K f hdim 3 1))
    (A B ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (e : tensor A B ≅ Stacks.Duality.dualizingSheafOverField f)
    (hB : invertibleCurveDegree K f hdim B = 8)
    (hξ : invertibleCurveDegree K f hdim ξ = 5)
    (t : ULift.{u} (Fin 2) → ξ.sections)
    (ht : Epi (MukaiPencilQuotient.pencilEvaluation ξ t)) :
    Module.finrank K (cohomologyOverField K f B 0) ≤ 3 := by
  let := modulesLinearOverField K f
  let := residualLine_isInvertible A ξ
  let := residualLine_isInvertible B ξ
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tensor B ξ) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible
      X.presheaf X.ringCatSheaf.2 B ξ
  have hA := other_degree_eight K f hdim hg A B e hB
  have hdA : invertibleCurveDegree K f hdim (residualLine A ξ) = 3 := by
    rw [residual_degree K f hdim, hA, hξ]
    norm_num
  have hdB : invertibleCurveDegree K f hdim (residualLine B ξ) = 3 := by
    rw [residual_degree K f hdim, hB, hξ]
    norm_num
  have hRA := M9StacksIntegration.CanonicalPencilBounds.h0_le_one_of_no_pencil
    f hdim 3 hno3 (residualLine A ξ) hdA
  have hRB := M9StacksIntegration.CanonicalPencilBounds.h0_le_one_of_no_pencil
    f hdim 3 hno3 (residualLine B ξ) hdB
  have hHom := hom_finrank_eq_residual_h0 K f A ξ
  have hSerre := MukaiRecognitionHomBound.finrank_residual_hom K f hdim ξ A B 1 e
  have hp := invertibleCurveDegree_tensorSheaf_eq_add K f hdim B ξ
  change invertibleCurveDegree K f hdim (tensor B ξ) =
    invertibleCurveDegree K f hdim B + invertibleCurveDegree K f hdim ξ at hp
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus K f hdim (tensor B ξ)
  rw [hp, hB, hξ, hg] at hRR
  have hPencil := MukaiBasepointFreePencilTrick.tensor_H0_inequality K f B ξ t ht
  change 2 * Module.finrank K (cohomologyOverField K f B 0) ≤
    Module.finrank K (cohomologyOverField K f (tensor B ξ) 0) +
      Module.finrank K (cohomologyOverField K f (residualLine B ξ) 0) at hPencil
  omega

/-- Both complete residual section counts are at most three in this genuine free case. -/
theorem residual_h0_bounds (hg : genus f = 9)
    (hno3 : ¬ Nonempty (LinearSeries K f hdim 3 1))
    (A B ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (e : tensor A B ≅ Stacks.Duality.dualizingSheafOverField f)
    (hB : invertibleCurveDegree K f hdim B = 8)
    (hξ : invertibleCurveDegree K f hdim ξ = 5)
    (t : ULift.{u} (Fin 2) → ξ.sections)
    (ht : Epi (MukaiPencilQuotient.pencilEvaluation ξ t)) :
    Module.finrank K (cohomologyOverField K f A 0) ≤ 3 ∧
      Module.finrank K (cohomologyOverField K f B 0) ≤ 3 := by
  have hA := other_degree_eight K f hdim hg A B e hB
  exact ⟨h0_le_three K f hdim hg hno3 B A ξ
      (MukaiTensorLineCancellation.tensorSwap B A ≪≫ e) hA hξ t ht,
    h0_le_three K f hdim hg hno3 A B ξ e hB hξ t ht⟩

end M9Native.MukaiFreeFiveResidualSections

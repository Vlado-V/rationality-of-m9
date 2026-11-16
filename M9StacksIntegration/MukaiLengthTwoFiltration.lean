module

public import M9StacksIntegration.MukaiCompleteEvaluation
public import M9StacksIntegration.MukaiPencilQuotient
public import M9StacksIntegration.MukaiDualSpanSectionCount
public import M9StacksIntegration.MukaiNetFromNoSeven
public import M9StacksIntegration.FiniteCurveDivisor

/-!
# The actual length-two defect gives Mukai's divisor sequence

For an actual length-two closed subscheme where the original net fails
to restrict surjectively, its Cartier property, the degree-six pencil,
both generating evaluations, and the dual-span filtration are derived.
The section count and inverse-twist vanishing then follow. The separate
genus-nine plane argument constructs this defect; it is not assumed to
be the conclusion of this intermediate theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace M9Native.MukaiLengthTwoFiltration

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open MukaiBundle MukaiDualSpanSections CurveDivisorSections CurveDivisorDegree

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- All the geometric pencil and evaluation hypotheses of the actual
divisor sequence follow from the original length-two restriction defect.
Neither final conclusion nor a degree-six pencil is supplied as input. -/
theorem count_and_vanishing_of_length_two_defect
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (hno7 : ∀ d : ℕ, d ≤ 7 → ¬ Nonempty (LinearSeries k f hdim d 2))
    (E : LinearSeries k f hdim 8 2)
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f E.L 0))
    (D : X.IdealSheafData) (hDdim : topologicalKrullDim D.subscheme ≤ 0)
    (hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (hfail : ¬ Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D E.L) 0))
    (α : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (hα : invertibleCurveDegree k f hdim α = 8) :
    Module.finrank k (cohomologyOverField k f
      (dualSpan E.L (completeNetSections f E.L bβ)) 0) = 3 ∧
      Subsingleton (cohomologyOverField k f
        (Scheme.Modules.tensorObj (dualSheaf α)
          (dualSpan E.L (completeNetSections f E.L bβ))) 0) := by
  let := E.isInvertible
  let hD := FiniteCurveDivisor.isEffectiveCartierDivisor_of_dimension_zero f D hDdim
  let := hD
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have hβ0 : Module.finrank k (cohomologyOverField k f E.L 0) = 3 := by
    simpa only [Fintype.card_ulift, Fintype.card_fin] using Module.finrank_eq_card_basis bβ
  let ξ : X.Modules := twistDown D E.L
  have hξdegree : invertibleCurveDegree k f hdim ξ = 6 := by
    change invertibleCurveDegree k f hdim (twistDown D E.L) = 6
    rw [twistDown_degree f hdim D E.L, E.degree_eq, hd]
    norm_num
  have hξlower := two_le_twistDown_h0_of_restriction_not_surjective f D hDdim E.L hd hβ0 hfail
  have hξupper := MukaiNetFromNoSeven.h0_le_two_of_degree_lt_eight f hdim
    (hno7 7 (by decide)) ξ (by rw [hξdegree]; decide)
  have hξ0 : Module.finrank k (cohomologyOverField k f ξ 0) = 2 :=
    le_antisymm hξupper hξlower
  let := invertible_cohomology_zero_finite f ξ
  let bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f ξ 0) :=
    (Module.finBasisOfFinrankEq k (cohomologyOverField k f ξ 0) hξ0).reindex Equiv.ulift.symm
  let Eξ : LinearSeries k f hdim 6 1 :=
    { L := ξ
      isInvertible := inferInstance
      degree_eq := hξdegree
      V := ⊤
      finrank_eq := by simpa only [finrank_top] using hξ0 }
  have heβ : Epi (netEvaluation E.L (completeNetSections f E.L bβ)) :=
    MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f hdim hno7 E bβ
  have heξ : Epi (MukaiPencilQuotient.pencilEvaluation ξ
      (MukaiPencilQuotient.completePencilSections f D E.L bξ)) := by
    change Epi (CompleteEvaluationGeneration.basisEvaluation f ξ bξ)
    exact MukaiCompleteEvaluation.degree_six_completePencilEvaluation_epi f hdim hnp Eξ bξ
  let S : ShortComplex X.Modules :=
    MukaiPencilQuotient.completePencilSequence f D E.L bξ bβ heξ heβ
  have hS := MukaiPencilQuotient.completePencilSequence_shortExact f D E.L bξ bβ heξ heβ
  have hA : invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) = 2 := by
    have h := invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D
    change invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) at h
    rw [hd] at h
    exact h
  have hA0 := divisorSheaf_h0_eq_one_of_degree_le_five f hdim hnp D
    (by rw [hA]; decide)
  exact MukaiDualSpanSectionCount.count_and_vanishing_of_exact_line_filtration f hdim
    α E.L (Stacks.Divisors.invertibleSheaf' D) ξ hα E.degree_eq hA hξdegree hA0 hξ0 bβ
    (completeNetSections f E.L bβ) heβ S.f S.g S.zero hS

end M9Native.MukaiLengthTwoFiltration

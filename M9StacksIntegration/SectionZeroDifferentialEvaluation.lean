module

public import M9StacksIntegration.ConormalDifferentialSections
public import M9StacksIntegration.LagrangianSmoothSectionConormal

/-!
# Actual differentials of equations of a section zero scheme

The native conormal map, precomposed with original dual-section
 evaluation, is pinned on actual ambient sections. Its value is the
 pulled universal differential of their actual evaluation against the
 original section. No conormal/differential identification is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionZeroDifferentialEvaluation

variable {X S : Scheme.{u}} (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
  (s : Γ(E, (⊤ : X.Opens))) (p : X ⟶ S)

/-- The actual equation-dual to pulled ambient differential morphism. -/
def differentialMap : SectionZeroConormal.sourceModule E s ⟶
    (Scheme.Modules.pullback (SectionZeroConormal.inclusion E s)).obj
      (Scheme.Hom.relativeDifferentials p) :=
  SectionZeroConormal.evaluationMap E s ≫
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge
      (SectionZeroConormal.inclusion E s)).inv ≫
    Stacks.ConormalSequenceRight.conormalDifferential
      (SectionZeroConormal.inclusion E s) p

/-- The class map used for the original zero ideal is the original native quotient map. -/
theorem idealClassMap_eq_canonical :
    SectionZeroConormal.idealClassMap E s =
      Stacks.Immersion.canonicalConormalQuotientMap (SectionZeroConormal.inclusion E s) := rfl

/-- Adjunction retains original evaluation and the genuine conormal first arrow. -/
theorem differentialMap_adjunction :
    (Scheme.Modules.pullbackPushforwardAdjunction (SectionZeroConormal.inclusion E s)).homEquiv _ _
      (differentialMap E s p) =
    SectionZeroEvaluation.evaluationIdealMap E s ≫
      Stacks.Immersion.canonicalConormalQuotientMap (SectionZeroConormal.inclusion E s) ≫
      (Scheme.Modules.pushforward (SectionZeroConormal.inclusion E s)).map
        ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge
            (SectionZeroConormal.inclusion E s)).inv ≫
          Stacks.ConormalSequenceRight.conormalDifferential
            (SectionZeroConormal.inclusion E s) p) := by
  let i := SectionZeroConormal.inclusion E s
  let D : SectionZeroConormal.conormalModule E s ⟶
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
      Stacks.ConormalSequenceRight.conormalDifferential i p
  change (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _
    (SectionZeroConormal.evaluationMap E s ≫ D) = _
  rw [Adjunction.homEquiv_naturality_right]
  rw [SectionZeroConormal.evaluationMap_adjunction, idealClassMap_eq_canonical]
  exact Category.assoc _ _ _

/-- The underlying actual ideal section is the original dual evaluation. -/
theorem idealSection_evaluation (U : X.Opens) (t : Γ(dualSheaf E, U)) :
    Stacks.Conormal.idealSection (SectionZeroConormal.inclusion E s) U
      ((SectionZeroEvaluation.evaluationIdealMap E s).val.app (op U) t) =
      evalAt E t (E.presheaf.map (homOfLE le_top).op s) :=
  SectionZeroEvaluation.evaluationIdealMap_eval E s U t

/-- On every original ambient section, the genuine conormal arrow is its actual differential. -/
theorem differentialMap_adjunction_apply (U : X.Opens) (t : Γ(dualSheaf E, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction
        (SectionZeroConormal.inclusion E s)).homEquiv _ _
        (differentialMap E s p)).val.app (op U)) t =
      (((Scheme.Modules.pullbackPushforwardAdjunction
          (SectionZeroConormal.inclusion E s)).unit.app
          (Scheme.Hom.relativeDifferentials p)).val.app (op U)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d
          (evalAt E t (E.presheaf.map (homOfLE le_top).op s))) := by
  rw [differentialMap_adjunction]
  exact (ConormalDifferentialSections.conormalDifferential_canonicalConormalQuotientMap
    (SectionZeroConormal.inclusion E s) p U
    ((SectionZeroEvaluation.evaluationIdealMap E s).val.app (op U) t)).trans
      (congrArg (fun a =>
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (SectionZeroConormal.inclusion E s)).unit.app
            (Scheme.Hom.relativeDifferentials p)).val.app (op U)).hom
          ((Scheme.Hom.universalRelativeDerivation p).d a))
        (idealSection_evaluation E s U t))

section Lagrangian

open LagrangianGrassmannian

variable (K : Type u) [Field K] (F : (space K).Modules)
  [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 5]

local instance : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F := hF.isFiniteLocallyFree

variable (t : Γ(F,⊤))
  [SmoothOfRelativeDimension 1 (SectionZeroConormal.inclusion F t ≫ projection K)]

/-- The normalized map is the literal first arrow of the actual equation conormal sequence. -/
theorem differentialMap_eq_equationSequence_f :
    differentialMap F t (projection K) =
      (LagrangianSmoothSectionConormal.equationSequence K F t).f := by
  simp only [differentialMap, LagrangianSmoothSectionConormal.equationSequence,
    LagrangianSmoothSectionConormal.equationConormalIso, Iso.trans_hom, Iso.symm_hom,
    LagrangianSmoothSectionConormal.conormalEvaluationIso_hom, Category.assoc]
  rfl

/-- Original smooth-section transversality uses exactly the differential of the original equation. -/
theorem equationSequence_f_adjunction_apply (U : (space K).Opens)
    (tau : Γ(dualSheaf F, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction
        (SectionZeroConormal.inclusion F t)).homEquiv _ _
        (LagrangianSmoothSectionConormal.equationSequence K F t).f).val.app (op U)) tau =
      (((Scheme.Modules.pullbackPushforwardAdjunction
          (SectionZeroConormal.inclusion F t)).unit.app
          (Scheme.Hom.relativeDifferentials (projection K))).val.app (op U)).hom
        ((Scheme.Hom.universalRelativeDerivation (projection K)).d
          (evalAt F tau (F.presheaf.map (homOfLE le_top).op t))) := by
  rw [← differentialMap_eq_equationSequence_f]
  exact differentialMap_adjunction_apply F t (projection K) U tau

end Lagrangian

end M9Native.SectionZeroDifferentialEvaluation

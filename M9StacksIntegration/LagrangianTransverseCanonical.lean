module

public import M9StacksIntegration.LagrangianOrderedFibre
public import M9StacksIntegration.LagrangianTransverseRestriction
public import M9StacksIntegration.LagrangianFibreAdjunction
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials

/-!
# The canonical line of the original transverse five-row cut

The literal ordered cut is compared with its actual five-equation bundle
zero scheme. Native adjunction and the native canonical/differential
comparison then give the original pulled determinant line, preserving
the original LG immersion. No line comparison or model is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianTransverseCanonical

open LagrangianTransverseRestriction LagrangianOrderedFibre LagrangianPluckerQuotient

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- The actual original differential line, obtained from the constructed
zero-scheme model with the original immersion retained. -/
def differentialsIsoCurveLine (hM : Function.Surjective M.mulVec) :
    Scheme.Hom.relativeDifferentials (curveProjection K M) ≅
      LagrangianPrimitiveRestriction.restrictedLine K (inclusion K M) :=
  LagrangianFibreAdjunction.differentialsIsoOfModel K (curveProjection K M)
      (LagrangianFibreFiveSection.fiveSection K M hM) (cutIsoModel K M hM)
      (cutIsoModel_hom_base K M hM) ≪≫
    (Scheme.Modules.pullbackCongr (cutIsoModel_hom_toLG K M hM)).app (determinantLine K)

/-- The original native canonical sheaf is the original determinant
restriction, with the model and all comparisons derived. -/
def canonicalIsoCurveLine (hM : Function.Surjective M.mulVec) :
    Stacks.Duality.dualizingSheafOverField (curveProjection K M) ≅
      LagrangianPrimitiveRestriction.restrictedLine K (inclusion K M) := by
  let : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  exact SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso (curveProjection K M) ≪≫
    differentialsIsoCurveLine K M hM

/-- The orientation used by the original primitive-to-canonical
restriction map. -/
def restrictedCanonicalIso (hM : Function.Surjective M.mulVec) :
    LagrangianPrimitiveRestriction.restrictedLine K (inclusion K M) ≅
      Stacks.Duality.dualizingSheafOverField (curveProjection K M) :=
  (canonicalIsoCurveLine K M hM).symm

end M9Native.LagrangianTransverseCanonical

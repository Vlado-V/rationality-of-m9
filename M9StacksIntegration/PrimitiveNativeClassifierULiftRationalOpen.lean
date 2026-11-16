module

public import M9StacksIntegration.ComplexStandaloneCoefficientTransport
public import M9StacksIntegration.PrimitiveNativeClassifierRationalOpen

@[expose] public section

/-! Type-0 coefficient transport of the actual native classifier
rational-open criterion. The independent target space and original
classifier geometry are retained. No quotient map or chart is supplied. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
attribute [local instance] Space.pointTopology

namespace M9Native.PrimitiveNativeClassifierULiftRationalOpen

open M9StacksIntegration.AllTestNativeOriginalFunctor

variable (B : BigFppfSite) (hC : B.Contains (Spec (.of ℂ)))
  (X : AlgebraicSpaces B (Spec (.of ℂ)) hC)

/-- Canonically relabel the original all-test space of the SAME independent
native target; no quotient space or alternative target is chosen. -/
def target : M9StandaloneDraft.Space (ULift.{0} ℂ) :=
  ComplexStandaloneCoefficientTransport.space
    (M9StacksIntegration.AllTestNativeOriginalSpace.originalSpaceOfNative
      ℂ B hC X.obj X.property)

theorem target_obj :
    (target B hC X).obj =
      StandaloneCoefficientFamilyTransport.presheafForward
        ComplexStandaloneCoefficientTransport.baseIso
        ((originalPresheafFunctor ℂ B hC).obj X) := rfl

variable (U : PrimitiveGrassmannianAction.space.Opens)
  (f : yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U) ⟶ X.obj)

/-- The frozen native criterion derives an actual common dense affine
open on the canonically relabeled SAME independent target. This asserts
only Type-0 transport and makes no universe-enlargement claim. -/
theorem rationalOpen
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC X.obj)
    (hft : Space.IsLocallyOfFiniteType B (Spec (.of ℂ)) hC
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of ℂ)) hC).from X.obj))
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : PrimitiveNativeClassifierRationalOpen.ClassifierGeometry B hC X U f) :
    M9StandaloneDraft.RationalOpen (ULift.{0} ℂ) 24 (target B hC X).obj :=
  ComplexStandaloneCoefficientTransport.rationalOpen 24 _
    (PrimitiveNativeClassifierRationalOpen.rationalOpen B hC X U f hInt hft hf h)

end M9Native.PrimitiveNativeClassifierULiftRationalOpen

module

public import M9StacksIntegration.NativeSchematicCurveClassifier
public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth

/-!
# The original universal section family as a native family of curves

The total and base are the literal inverse-image and good-open schemes
of the original universal five-hyperplane projection. Properness and
smoothness of relative dimension one are the proved geometric theorems
of that same projection. The native family and its cartesian classifying
functor are constructed, not assumed.

This gives the map to `Curves`. Geometric connectedness and genus nine,
and hence the factorization to the native genus-nine substack, remain
separate geometric obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.UniversalLagrangianCurveFamily

open CategoryTheory AlgebraicGeometry
open M9StacksIntegration.NativeSchematicCurveFamily
open M9StacksIntegration.NativeSchematicCurveClassifier
open M9Native.LagrangianLinearSections M9Native.LagrangianLinearSectionGenericSmooth

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
variable (K : Type u) [Field K]

/-- The original restricted projection, viewed in the chosen native site. -/
def siteProjection (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    siteObject B integerBase hZ hV
        (specULiftZIsTerminal.from ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) ⟶
      siteObject B integerBase hZ hU (specULiftZIsTerminal.from (goodOpen K).toScheme) :=
  Over.homMk (ObjectProperty.homMk (restrictedProjection K))
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The native family uses the original restricted total, base and map.
Only containment in the chosen native site is parameterized. -/
def family [CharZero K] (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) : CurveFamily B hZ :=
  properSmoothSchemeFamily B hZ (siteProjection B hZ K hU hV)
    (by change IsProper (restrictedProjection K); infer_instance)
    (by change SmoothOfRelativeDimension 1 (restrictedProjection K); infer_instance)

/-- The actual original universal family has its native cartesian
classifying functor; no family-class or classifying-map premise occurs. -/
def classifyingMor [CharZero K] (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    Functor.FiberedMor (curvesProjectionOver B hZ) (family B hZ K hU hV).base :=
  properSmoothClassifyingMor B hZ (siteProjection B hZ K hU hV)
    (by change IsProper (restrictedProjection K); infer_instance)
    (by change SmoothOfRelativeDimension 1 (restrictedProjection K); infer_instance)

/-- Identity-fibre evaluation recovers the same original native family. -/
def classifiesOriginalFamily [CharZero K] (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    (classifyingMor B hZ K hU hV).toFunctor.obj
        (Functor.FiberedMor.unit (family B hZ K hU hV).base) ≅ family B hZ K hU hV :=
  M9StacksIntegration.NativeSchematicCurveClassifier.classifiesOriginalFamily B hZ
    (siteProjection B hZ K hU hV)
    (by change IsProper (restrictedProjection K); infer_instance)
    (by change SmoothOfRelativeDimension 1 (restrictedProjection K); infer_instance)

end M9Native.UniversalLagrangianCurveFamily

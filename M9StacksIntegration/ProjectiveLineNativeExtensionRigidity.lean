module

public import M9StacksIntegration.StandardCurveCotangentExt
public import M9StacksIntegration.ProjectiveLineTangentCohomology
public import M9StacksIntegration.CurveP1NormalSections

/-!
# Actual standard cotangent extension rigidity of native P1

Actual Euler cohomology and original line Riemann--Roch already give
H1 of the literal projective-line tangent sheaf zero. The genuine smooth
standard-model comparison now proves that the original geometric
cotangent extension class group is zero. No rigidity/class vanishing
premise or deformation-category comparison is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpaceThickening
open M9Native.PencilProjectiveLineGeometry

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] isCurve_projectiveSpaceOver_one M9Native.CurveP1NormalSections.line_smooth

universe u

namespace M9Native.ProjectiveLineNativeExtensionRigidity

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The original standard geometric class group on native P1 is trivial. -/
theorem native_ext_one_subsingleton :
    Subsingleton (extOneNaiveCotangent (toBase k).toLRSHom.toShHom
      (InvertibleExtCancellation.unit (Line k))) := by
  let := modulesLinearOverField k (toBase k)
  let := StandardCurveCotangentExt.nativeExtModule (toBase k)
    (InvertibleExtCancellation.unit (Line k))
  let := ModuleCat.subsingleton_of_isZero
    (ProjectiveLineTangentCohomology.line_tangent_h1_isZero k)
  exact (StandardCurveCotangentExt.tangentOneLinearEquiv (toBase k)).injective.subsingleton

/-- Every actual native target class is zero, without a class premise. -/
theorem native_ext_one_eq_zero
    (ξ : extOneNaiveCotangent (toBase k).toLRSHom.toShHom
      (InvertibleExtCancellation.unit (Line k))) : ξ = 0 := by
  let := native_ext_one_subsingleton k
  exact Subsingleton.elim _ _

/-- Changing an actual coefficient sheaf by an actual isomorphism to
O preserves the proved native target rigidity. -/
theorem native_ext_one_eq_zero_of_coefficient_iso (G : (Line k).Modules)
    (e : G ≅ InvertibleExtCancellation.unit (Line k))
    (ξ : extOneNaiveCotangent (toBase k).toLRSHom.toShHom G) : ξ = 0 := by
  let E := (shiftFunctor (DerivedCategory (Line k).Modules) (1 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor (Line k).Modules 0).mapIso e)
  apply (cancel_mono E.hom).mp
  simpa only [zero_comp] using native_ext_one_eq_zero k (ξ ≫ E.hom)

end M9Native.ProjectiveLineNativeExtensionRigidity

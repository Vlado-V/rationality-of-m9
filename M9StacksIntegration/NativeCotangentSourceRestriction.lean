module

public import M9StacksIntegration.NativeCotangentDerivedProjection
public import M9StacksIntegration.CurveDerivativeNormal

/-!
# Original cotangent restriction is the actual derivative on source H1

The actual direct native arrow is used throughout. Its checked native
normalization, together with the original evaluation-natural Ext/H1
comparison, identifies actual restricted classes with the literal H1
of the dual native differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace M9Native.NativeCotangentSourceRestriction

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y)
  [Smooth pY] [Smooth (g ≫ pY)]
  [IsCurve k pY] [IsCurve k (g ≫ pY)]

/-- The original direct derived cotangent arrow, rather than the
separate tower-based comparison implementation. -/
abbrev directArrow := derivedPullbackNaiveCotangentMap
  g.toLRSHom.toShHom pY.toLRSHom.toShHom

/-- Actual original restriction of a class is the actual H1 dual
derivative under the exact native source-class comparison. -/
theorem restriction_tangentOne
    (ξ : extOneNaiveCotangent (g ≫ pY).toLRSHom.toShHom
      (InvertibleExtCancellation.unit X)) :
    letI := modulesLinearOverField k (g ≫ pY)
    letI := StandardCurveCotangentExt.nativeExtModule (g ≫ pY) (InvertibleExtCancellation.unit X)
    letI := StandardCotangentArrow.pulledExtModule (g ≫ pY) pY g
      (InvertibleExtCancellation.unit X)
    StandardCotangentArrow.pulledTangentOneLinearEquiv (g ≫ pY) pY g
        (directArrow pY g ≫ ξ) =
      cohomologyOverFieldMap k (g ≫ pY)
        (CurveDerivativeNormal.tangentMap (g ≫ pY) pY g rfl) 1
        (StandardCurveCotangentExt.tangentOneLinearEquiv (g ≫ pY) ξ) := by
  let := modulesLinearOverField k (g ≫ pY)
  let := StandardCurveCotangentExt.nativeExtModule (g ≫ pY) (InvertibleExtCancellation.unit X)
  let := StandardCotangentArrow.pulledExtModule (g ≫ pY) pY g
    (InvertibleExtCancellation.unit X)
  exact (StandardCotangentArrow.restriction_tangentOne (g ≫ pY) pY g
    (directArrow pY g) ξ).trans
      (congrArg (fun a => cohomologyOverFieldMap k (g ≫ pY) (dualMap a) 1
        (StandardCurveCotangentExt.tangentOneLinearEquiv (g ≫ pY) ξ))
          (NativeCotangentDerivedProjection.normalizedMap_eq pY g))

/-- Zero original restricted class is exactly zero under the literal
dual-derivative H1 map, with no source-image assumption. -/
theorem restriction_eq_zero_iff
    (ξ : extOneNaiveCotangent (g ≫ pY).toLRSHom.toShHom
      (InvertibleExtCancellation.unit X)) :
    letI := modulesLinearOverField k (g ≫ pY)
    letI := StandardCurveCotangentExt.nativeExtModule (g ≫ pY) (InvertibleExtCancellation.unit X)
    directArrow pY g ≫ ξ = 0 ↔
      cohomologyOverFieldMap k (g ≫ pY)
        (CurveDerivativeNormal.tangentMap (g ≫ pY) pY g rfl) 1
        (StandardCurveCotangentExt.tangentOneLinearEquiv (g ≫ pY) ξ) = 0 := by
  let := modulesLinearOverField k (g ≫ pY)
  let := StandardCurveCotangentExt.nativeExtModule (g ≫ pY) (InvertibleExtCancellation.unit X)
  let := StandardCotangentArrow.pulledExtModule (g ≫ pY) pY g
    (InvertibleExtCancellation.unit X)
  rw [← restriction_tangentOne pY g ξ]
  exact (StandardCotangentArrow.pulledTangentOneLinearEquiv (g ≫ pY) pY g).map_eq_zero_iff.symm

end M9Native.NativeCotangentSourceRestriction

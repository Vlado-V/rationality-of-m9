module

public import M9StacksIntegration.NativeSchematicCurveFamily
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered

/-!
# Classifying an original schematic relative curve

The native 2-Yoneda construction turns the actual family of an original
proper smooth relative curve into a cartesian classifying functor. Its
value over the identity of the original base is isomorphic to that same
family. No classifying map or native family-class premise is supplied.

This constructs the map to `Curves`. Factoring it through the genuine
smooth-genus-nine subcategory additionally requires the actual universal
H0 and genus-nine proofs; those are not asserted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9StacksIntegration.NativeSchematicCurveClassifier

open CategoryTheory AlgebraicGeometry NativeSchematicCurveFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The original schematic family determines an actual cartesian
classifying functor on the slice over its original base. -/
def properSmoothClassifyingMor {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T)
    (hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hs : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q)) :
    Functor.FiberedMor (curvesProjectionOver B hZ) T := by
  let : (curvesProjectionOver B hZ).IsFibered :=
    (curvesFiberedCategory B hZ).2.isFibered
  exact Functor.FiberedMor.OfFiberObj.fiberedMor (curvesProjectionOver B hZ) T
    (show (curvesProjectionOver B hZ).obj
      (properSmoothSchemeFamily B hZ q hp hs) = T from rfl)

/-- The classifying functor classifies the original family, rather
than an unrelated object with the same numerical invariants. -/
def classifiesOriginalFamily {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T)
    (hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hs : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q)) :
    (properSmoothClassifyingMor B hZ q hp hs).toFunctor.obj
        (Functor.FiberedMor.unit T) ≅ properSmoothSchemeFamily B hZ q hp hs := by
  let : (curvesProjectionOver B hZ).IsFibered :=
    (curvesFiberedCategory B hZ).2.isFibered
  exact Functor.Fiber.fiberInclusion.mapIso
    (Functor.FiberedMor.OfFiberObj.fiberIso (curvesProjectionOver B hZ) T
      (show (curvesProjectionOver B hZ).obj
        (properSmoothSchemeFamily B hZ q hp hs) = T from rfl)
      (properSmoothClassifyingMor B hZ q hp hs).obj_over_unit)

end M9StacksIntegration.NativeSchematicCurveClassifier

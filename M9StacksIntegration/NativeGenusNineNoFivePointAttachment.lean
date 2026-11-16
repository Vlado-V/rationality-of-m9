module

public import M9StacksIntegration.NativeGenusNineNoFivePoints
public import M9StacksIntegration.NativeSmoothGenusSourceFullness

/-! Original family arrows attach actual native source points to the
actual no-five representative locus. Only genuine endpoint base equalities
and the given physical family's actual raw arrow are used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeGenusNineNoFivePointAttachment
open NativeGenusNineNoFivePoints NativeStackCoverageDenseImage

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (d : CurveDatum B hZ K hK)
  (p : Stack.FieldValuedPoint B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)).val.val)
  (hp : p.base = d.base)
  (β : (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK 9 (by decide)).obj p.obj ⟶
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK 9 (by decide)).obj d.fieldPoint.obj)
  (hβ : (curvesProjectionOver B hZ).IsHomLift
    (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj d.base)) β)

include d hp β hβ

/-- Actual original vertical family arrows give equality of the actual
native source point and the original curve's constructed classifier point. -/
theorem point_eq_of_raw_arrow :
    Stack.pointClass B (Spec (.of K)) hK _ _ p = d.nativePoint :=
  pointClass_eq_of_arrow B (Spec (.of K)) hK p d.fieldPoint
    (NativeSmoothGenusSourceFullness.liftRawArrow B hZ 9 (by decide) K hK d.base
      (p.over.trans hp) d.fieldPoint.over β hβ)

/-- The derived source-point equality attaches the actual field-family
point to the representative-existential no-five locus. -/
theorem mem_locus_of_raw_arrow :
    Stack.pointClass B (Spec (.of K)) hK _ _ p ∈ locus B hZ K hK :=
  ⟨d, point_eq_of_raw_arrow B hZ K hK d p hp β hβ⟩

end M9Native.NativeGenusNineNoFivePointAttachment

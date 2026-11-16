module

public import M9StacksIntegration.NativeStackCoverageDenseImage
public import M9StacksIntegration.NativeSmoothGenusCoarseMap
public import M9StacksIntegration.AllTestSchemeCurveConstants

/-! The actual chosen-source points which admit a bounded original
algebraically closed genus-nine curve with no degree-five pencil.
This locus is defined by genuine original curve data and the constructed
native classifier. Its density is a separate geometric theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeGenusNineNoFivePoints
open M9StacksIntegration.AllTestSchemeCurveConstants

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- A real original curve in the native site over an algebraically closed
extension field, with the actual no-five-pencil condition. -/
structure CurveDatum where
  carrier : Type u
  [field : Field carrier]
  [isAlgClosed : IsAlgClosed carrier]
  [charZero : CharZero carrier]
  coefficient : K →+* carrier
  contained : B.Contains (Spec (.of carrier))
  total : BigFppfOver B integerBase hZ
  projection : total ⟶ (Over.map
    (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj
      (siteObject B (Spec (.of K)) hK contained (Spec.map (CommRingCat.ofHom coefficient)))
  schemeCurve : M9StandaloneDraft.SchemeCurve
    ((BigFppfOver.toScheme B integerBase hZ).map projection) 9
  noFive : letI : IsProper ((BigFppfOver.toScheme B integerBase hZ).map projection) := schemeCurve.1
    ¬ Nonempty (LinearSeries carrier
    ((BigFppfOver.toScheme B integerBase hZ).map projection)
    (schemeCurve_field_geometry
      ((BigFppfOver.toScheme B integerBase hZ).map projection) schemeCurve).2.1.le 5 1)

attribute [instance] CurveDatum.field CurveDatum.isAlgClosed CurveDatum.charZero

namespace CurveDatum
variable {B hZ K hK} (d : CurveDatum B hZ K hK)

def base : BigFppfOver B (Spec (.of K)) hK :=
  siteObject B (Spec (.of K)) hK d.contained (Spec.map (CommRingCat.ofHom d.coefficient))

/-- The actual identity field point of the datum's own field base. -/
def identityPoint : Space.FieldValuedPoint B (Spec (.of K)) hK (schemeSpace d.base).obj where
  carrier := d.carrier
  contained := d.contained
  toBase := Spec.map (CommRingCat.ofHom d.coefficient)
  value := 𝟙 d.base

/-- The constructed classifier to the SAME independently chosen source. -/
def classifier : BasedCategory.ofFunctor (Over.forget d.base) ⥤ᵇ
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)).val.val :=
  NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK d.base
    d.projection 9 (by decide) d.schemeCurve

def fieldPoint : Stack.FieldValuedPoint B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)).val.val :=
  NativeStackCoverageDenseImage.classifierFieldPoint B (Spec (.of K)) hK
    (X := M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide))
    d.classifier d.identityPoint

/-- The genuine native source-stack class represented by the original curve. -/
def nativePoint : Stack.AlgebraicStacks.points B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)) :=
  Stack.pointClass B (Spec (.of K)) hK _ _ d.fieldPoint

end CurveDatum

/-- Native points admitting such an actual ACL original curve representative. -/
def locus : Set (Stack.AlgebraicStacks.points B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide))) :=
  {z | ∃ d : CurveDatum B hZ K hK, z = d.nativePoint}

/-- Every constructed datum belongs to this actual representative locus. -/
theorem CurveDatum.mem_locus (d : CurveDatum B hZ K hK) : d.nativePoint ∈ locus B hZ K hK :=
  ⟨d, rfl⟩

end M9Native.NativeGenusNineNoFivePoints

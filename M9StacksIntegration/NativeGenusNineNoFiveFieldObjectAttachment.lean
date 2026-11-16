module

public import M9StacksIntegration.NativeGenusNineFieldObjectCurve
public import M9StacksIntegration.NativeGenusNineNoFivePointAttachment
import all M9StacksIntegration.NativeGenusNineNoFivePointAttachment

/-! The exact extracted original no-five curve attaches its actual native
source object to the representative locus. The curve, native projection,
whole scheme-curve property and classifier-unit comparison are all derived
by the actual field-object factory. Only original noFive is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeGenusNineNoFiveFieldObjectAttachment
open NativeGenusNineNoFivePoints

universe u

private theorem noFive_of_hom_eq {F : Type u} [Field F] {X : Scheme.{u}}
    (f g : X ⟶ Spec (.of F)) (hp : IsProper f) (hq : IsProper g)
    (e : f = g) (hd : topologicalKrullDim X ≤ 1)
    (hnp : letI : IsProper g := hq
      ¬ Nonempty (LinearSeries F g hd 5 1)) :
    letI : IsProper f := hp
    ¬ Nonempty (LinearSeries F f hd 5 1) := by
  subst g
  exact hnp

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (L : Type u) [Field L] [IsAlgClosed L] [CharZero L]
  (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)
  (z : (NativeGenusNineFieldObjectCurve.source B hZ K hK).val.val.obj)
  (hz : (NativeGenusNineFieldObjectCurve.source B hZ K hK).val.val.p.obj z =
    NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient)

/-- The honest remaining geometric condition, on the EXACT original
curve extracted from this actual source object. Properness is derived. -/
def NoFive : Prop :=
  letI : IsProper (NativeGenusNineFieldObjectCurve.original
    B hZ K hK L hL coefficient z hz).hom :=
      (NativeGenusNineFieldObjectCurve.model B hZ K hK L hL coefficient z hz).proper
  ∀ hd : topologicalKrullDim (NativeGenusNineFieldObjectCurve.original
      B hZ K hK L hL coefficient z hz).left ≤ 1,
    ¬ Nonempty (LinearSeries L (NativeGenusNineFieldObjectCurve.original
      B hZ K hK L hL coefficient z hz).hom hd 5 1)

/-- Build the actual datum; no datum, native model or comparison premise
is supplied by the caller. -/
def datum (hnp : NoFive B hZ K hK L hL coefficient z hz) : CurveDatum B hZ K hK where
  carrier := L
  coefficient := coefficient
  contained := hL
  total := NativeGenusNineFieldObjectCurve.nativeTotal B hZ K hK L hL coefficient z hz
  projection := NativeGenusNineFieldObjectCurve.nativeProjection B hZ K hK L hL coefficient z hz
  schemeCurve := NativeGenusNineFieldObjectCurve.nativeProjection_schemeCurve
    B hZ K hK L hL coefficient z hz
  noFive := by
    exact noFive_of_hom_eq
      ((BigFppfOver.toScheme B integerBase hZ).map
        (NativeGenusNineFieldObjectCurve.nativeProjection B hZ K hK L hL coefficient z hz))
      (NativeGenusNineFieldObjectCurve.original B hZ K hK L hL coefficient z hz).hom
      (NativeGenusNineFieldObjectCurve.nativeProjection_schemeCurve
        B hZ K hK L hL coefficient z hz).1
      (NativeGenusNineFieldObjectCurve.model B hZ K hK L hL coefficient z hz).proper
      (NativeGenusNineFieldObjectCurve.nativeProjection_original B hZ K hK L hL coefficient z hz)
      _ (hnp _)

/-- The actual field object, with its unchanged original coefficient. -/
def fieldPoint : Stack.FieldValuedPoint B (Spec (.of K)) hK
    (NativeGenusNineFieldObjectCurve.source B hZ K hK).val.val where
  carrier := L
  base := NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient
  isSpec := Iso.refl _
  obj := z
  «over» := hz

attribute [local implicit_reducible] datum
  NativeGenusNineNoFivePoints.CurveDatum.base
  NativeGenusNineNoFivePoints.CurveDatum.classifier
  NativeGenusNineNoFivePoints.CurveDatum.identityPoint
  NativeGenusNineNoFivePoints.CurveDatum.fieldPoint
  NativeGenusNineNoFivePoints.CurveDatum.nativePoint

/-- The genuine factory classifier-unit Iso and true source fullness
derive equality with the internally constructed representative. -/
theorem point_eq_datum (hnp : NoFive B hZ K hK L hL coefficient z hz) :
    Stack.pointClass B (Spec (.of K)) hK _ _
        (fieldPoint B hZ K hK L hL coefficient z hz) =
      (datum B hZ K hK L hL coefficient z hz hnp).nativePoint := by
  exact NativeGenusNineNoFivePointAttachment.point_eq_of_raw_arrow
    B hZ K hK (datum B hZ K hK L hL coefficient z hz hnp)
    (fieldPoint B hZ K hK L hL coefficient z hz) rfl
    (NativeGenusNineFieldObjectCurve.rawClassifierIso B hZ K hK L hL coefficient z hz).hom
    (NativeGenusNineFieldObjectCurve.rawClassifierIso_lift B hZ K hK L hL coefficient z hz)

/-- No-five on the exact extracted original model implies actual native
locus membership, with every model/comparison datum derived internally. -/
theorem mem_locus (hnp : NoFive B hZ K hK L hL coefficient z hz) :
    Stack.pointClass B (Spec (.of K)) hK _ _
        (fieldPoint B hZ K hK L hL coefficient z hz) ∈ locus B hZ K hK :=
  ⟨datum B hZ K hK L hL coefficient z hz hnp,
    point_eq_datum B hZ K hK L hL coefficient z hz hnp⟩

end M9Native.NativeGenusNineNoFiveFieldObjectAttachment

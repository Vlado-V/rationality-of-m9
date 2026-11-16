module

public import M9StacksIntegration.GenusNineNoFiveAtlasOpen
public import M9StacksIntegration.NativeGenusNineNoFiveFieldObjectAttachment
public import M9StacksIntegration.NativeAtlasGroundFieldDensity

@[expose] public section

/-! Density of the actual original no-five representative locus in the
actual chosen genus-nine source stack. Actual bounded-cover image
avoidance supplies chart opens, actual original ground-field curves
supply representatives, and the genuine native atlas point cover
descends their density. No density or target-integrality premise occurs. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.GenusNineNoFiveDensity

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))

/-- The actual no-five locus is dense on each actual original integral
chart component. Closed ground-field points give the exact original
curve representatives, so no unproved no-five base-change step is used. -/
theorem dense_component_preimage
    (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    Dense ((SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK
      (GenusNineCoverFamilyPullback.targetMap B hZ K hK x)) ⁻¹'
        NativeGenusNineNoFivePoints.locus B hZ K hK) := by
  letI : LocallyOfFiniteType (B.inclusion.map
      (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).hom) :=
    (GenusNineIntegralAtlas.component_structural_properties B hZ K hK x).2.2
  obtain ⟨U,hU,hno⟩ := GenusNineNoFiveAtlasOpen.exists_component_groundOpen B hZ K hK x
  apply NativeAtlasGroundFieldDensity.dense_chart_preimage_of_groundPoints B hK
    (V := GenusNineCoverFamilyPullback.targetSite B hZ K hK x)
    (GenusNineCoverFamilyPullback.targetMap B hZ K hK x)
    (NativeGenusNineNoFivePoints.locus B hZ K hK) U hU
  intro a ha hp
  rw [NativeChartFieldPointDictionary.schemePointMap_groundFieldPoint B hK
    (U := GenusNineCoverFamilyPullback.targetSite B hZ K hK x) a ha
    (GenusNineCoverFamilyPullback.targetMap B hZ K hK x)]
  let v := (NativeChartFieldPointDictionary.groundFieldPoint B hK
    (U := GenusNineCoverFamilyPullback.targetSite B hZ K hK x) a ha).value
  let z := NativeCoverPointDataOfFieldCurve.targetObject B hZ K hK
    (GenusNineCoverFamilyPullback.targetSite B hZ K hK x)
    (GenusNineCoverFamilyPullback.targetMap B hZ K hK x) K hK (RingHom.id K) v
  let hz := NativeCoverPointDataOfFieldCurve.targetObject_base B hZ K hK
    (GenusNineCoverFamilyPullback.targetSite B hZ K hK x)
    (GenusNineCoverFamilyPullback.targetMap B hZ K hK x) K hK (RingHom.id K) v
  have hnp : NativeGenusNineNoFiveFieldObjectAttachment.NoFive B hZ K hK
      K hK (RingHom.id K) z hz := by
    intro hd
    exact hno a ha hp hd
  exact NativeGenusNineNoFiveFieldObjectAttachment.mem_locus B hZ K hK
    K hK (RingHom.id K) z hz hnp

/-- Actual componentwise cover-image avoidance proves density of the
actual original no-five representative locus in the SAME independently
chosen native genus-nine stack. All bounded models, cover schemes,
source comparisons and chart coverage are constructed internally. -/
theorem locus_dense :
    @Dense _ (Stack.pointTopology B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
        B hZ K hK 9 (by decide)).val)
      (NativeGenusNineNoFivePoints.locus B hZ K hK) := by
  obtain ⟨t,ht⟩ := GenusNineIntegralAtlas.exists_finite_component_cover B hZ K hK
  apply NativeAtlasPointDensity.dense_of_chart_point_cover B (Spec (.of K)) hK
    (fun x => GenusNineCoverFamilyPullback.targetSite B hZ K hK x)
    (fun x => GenusNineCoverFamilyPullback.targetMap B hZ K hK x)
    ?_ (NativeGenusNineNoFivePoints.locus B hZ K hK)
    (fun x => dense_component_preimage B hZ K hK x)
  intro z
  obtain ⟨x,_,hx⟩ := ht z
  exact ⟨x,hx⟩

end M9Native.GenusNineNoFiveDensity
end

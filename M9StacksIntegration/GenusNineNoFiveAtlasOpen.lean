module

public import M9StacksIntegration.GenusNineCoverFamilyPullback
public import M9StacksIntegration.GenusNineNoFiveInAvoidedOpen
public import M9StacksIntegration.NativeChartFieldPointDictionary

@[expose] public section

/-! Every actual integral atlas component has an actual dense open whose
original algebraically closed field curves have no degree-five pencil.
All models, cover schemes, target geometry and native comparisons are
constructed; no nonpentagonal density or target integrality is assumed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.GenusNineNoFiveAtlasOpen

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))

/-- The true bounded-cover construction supplies the actual dense open
on every actual integral component, together with the no-five condition
on every contained algebraically closed original field representative. -/
theorem exists_component_open (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    ∃ U : (B.inclusion.obj
      (GenusNineCoverFamilyPullback.targetFamily B hZ K hK x).base.left).Opens,
      Dense (U : Set (B.inclusion.obj
        (GenusNineCoverFamilyPullback.targetFamily B hZ K hK x).base.left)) ∧
      (U : Set (B.inclusion.obj
        (GenusNineCoverFamilyPullback.targetFamily B hZ K hK x).base.left)).Nonempty ∧
      ∀ (L : Type u) [Field L] [IsAlgClosed L] [CharZero L]
        (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)
        (v : NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient ⟶
          GenusNineCoverFamilyPullback.targetSite B hZ K hK x),
        GenusNineNoFiveInAvoidedOpen.targetPoint B hZ K hK
          (GenusNineCoverFamilyPullback.targetMap B hZ K hK x)
          L hL coefficient v (IsLocalRing.closedPoint L) ∈ U →
        GenusNineNoFiveInAvoidedOpen.NoFiveAt B hZ K hK
          (GenusNineCoverFamilyPullback.targetMap B hZ K hK x)
          L hL coefficient v := by
  obtain ⟨m,t,n,D,P,hcov⟩ := GenusNineFiniteCoverSystem.exists_finite_system K B hK
  have hs := GenusNineIntegralAtlas.component_structural_properties B hZ K hK x
  letI : QuasiCompact (B.inclusion.map
      (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).hom) := hs.2.1
  letI : LocallyOfFiniteType (B.inclusion.map
      (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).hom) := hs.2.2
  letI : IsIntegral (B.inclusion.obj
      (GenusNineCoverFamilyPullback.targetFamily B hZ K hK x).base.left) :=
    GenusNineCoverFamilyPullback.target_integral B hZ K hK x
  letI : LocallyOfFiniteType (GenusNineCoverFamilyPullback.targetStructure B hZ K hK x) :=
    (GenusNineCoverFamilyPullback.target_structural_properties B hZ K hK x).2.2
  exact GenusNineNoFiveInAvoidedOpen.exists_dense_open_noFive B hZ K hK
    (GenusNineCoverFamilyPullback.targetMap B hZ K hK x) D P
    (GenusNineCoverFamilyPullback.target_classifier_smooth B hZ K hK x) hcov

/-- Transport to the actual original chart scheme retains the canonical
ground-field representative and its exact coefficient, rather than
changing the field of definition of the original curve. -/
theorem exists_component_groundOpen
    (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    ∃ U : (B.inclusion.obj
      (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).left).Opens,
      Dense (U : Set (B.inclusion.obj
        (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).left)) ∧
      ∀ (a : Spec (.of K) ⟶ B.inclusion.obj
          (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).left)
        (ha : a ≫ B.inclusion.map
          (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).hom = 𝟙 _),
        a (IsLocalRing.closedPoint K) ∈ U →
        GenusNineNoFiveInAvoidedOpen.NoFiveAt B hZ K hK
          (GenusNineCoverFamilyPullback.targetMap B hZ K hK x) K hK (RingHom.id K)
          (NativeChartFieldPointDictionary.groundFieldPoint B hK
            (U := GenusNineCoverFamilyPullback.targetSite B hZ K hK x) a ha).value := by
  obtain ⟨U,hd,_,hno⟩ := exists_component_open B hZ K hK x
  let e := eqToIso (BoundedCoverAtlasPointImage.targetBaseEquality B hZ K hK
    (GenusNineCoverFamilyPullback.targetMap B hZ K hK x))
  let U' := TopologicalSpace.Opens.comap ⟨e.inv, e.inv.continuous⟩ U
  have hd' : Dense (U' : Set (B.inclusion.obj
      (GenusNineCoverFamilyPullback.targetSite B hZ K hK x).left)) :=
    hd.preimage e.inv.homeomorph.isOpenMap
  refine ⟨U',hd',?_⟩
  intro a ha hp
  apply hno K hK (RingHom.id K)
    (NativeChartFieldPointDictionary.groundFieldPoint B hK
            (U := GenusNineCoverFamilyPullback.targetSite B hZ K hK x) a ha).value
  have hv : B.inclusion.map
      (NativeChartFieldPointDictionary.groundFieldPoint B hK
            (U := GenusNineCoverFamilyPullback.targetSite B hZ K hK x) a ha).value.left = a :=
    NativeChartFieldPointDictionary.groundFieldPoint_value B hK
      (U := GenusNineCoverFamilyPullback.targetSite B hZ K hK x) a ha
  change (B.inclusion.map
      (NativeChartFieldPointDictionary.groundFieldPoint B hK
            (U := GenusNineCoverFamilyPullback.targetSite B hZ K hK x) a ha).value.left ≫ e.inv)
    (IsLocalRing.closedPoint K) ∈ U
  rw [hv]
  exact hp

end M9Native.GenusNineNoFiveAtlasOpen
end

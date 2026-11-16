module

public import M9StacksIntegration.AllTestNativeOriginalFamily
public import M9StacksIntegration.AllTestNativeFamilyFull

/-! Actual inverse family comparison on arrows. A genuine native family
arrow over the specified original coefficient map yields a unique Cartesian
arrow between the constructed full-original families. Its native total map
is the actual conjugation by the proved recovery isomorphisms. No original
arrow, comparison equivalence or Cartesian square is supplied as a premise. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9StacksIntegration.AllTestNativeOriginalFamilyNaturality
open AllTestBoundedCharts AllTestNativeCurveFamily
  AllTestNativeCurveNaturality AllTestNativeOriginalFamily

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The inverse recovery map retains the same specified original base. -/
theorem originalFamilyNativeIso_inv_baseMap
    (T : BigFppfOver B (Spec (.of K)) hK) (F : CurveFamily B hZ)
    (hbase : F.base = nativeBase B hZ K hK T) (g : ℕ)
    (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F) :
    (originalFamilyNativeIso B hZ K hK T F hbase g hF).inv.baseMap =
      eqToHom hbase := by
  let e := originalFamilyNativeIso B hZ K hK T F hbase g hF
  have h := congrArg (fun a : F ⟶ F => a.baseMap) e.inv_hom_id
  change e.inv.baseMap ≫ e.hom.baseMap = 𝟙 F.base at h
  rw [originalFamilyNativeIso_baseMap B hZ K hK T F hbase g hF] at h
  apply (cancel_mono (eqToHom hbase.symm)).mp
  exact h.trans (by simp)

variable (T U : BigFppfOver B (Spec (.of K)) hK)
  (F G : CurveFamily B hZ)
  (hbaseF : F.base = nativeBase B hZ K hK T)
  (hbaseG : G.base = nativeBase B hZ K hK U)
  (g : ℕ) (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F)
  (hG : IsSmoothH0FamilyOfFibreGenus B hZ g G)

/-- The actual native arrow between the recoveries, using the genuine
recovery isomorphisms on both ends. -/
def comparisonArrow (δ : G ⟶ F) :
    nativeCurveFamily B hZ K hK (originalFamily B hZ K hK U G hbaseG g hG) ⟶
      nativeCurveFamily B hZ K hK (originalFamily B hZ K hK T F hbaseF g hF) :=
  (originalFamilyNativeIso B hZ K hK U G hbaseG g hG).hom ≫ δ ≫
    (originalFamilyNativeIso B hZ K hK T F hbaseF g hF).inv

/-- The conjugated arrow has exactly the specified native image of the
original field-base arrow; all base transports cancel. -/
theorem comparisonArrow_baseMap (a : U ⟶ T) (δ : G ⟶ F)
    (hδ : δ.baseMap = eqToHom hbaseG ≫
      (Over.map (fieldToInteger B hZ K hK)).map a ≫ eqToHom hbaseF.symm) :
    (comparisonArrow B hZ K hK T U F G hbaseF hbaseG g hF hG δ).baseMap =
      (Over.map (fieldToInteger B hZ K hK)).map a := by
  change (originalFamilyNativeIso B hZ K hK U G hbaseG g hG).hom.baseMap ≫
    δ.baseMap ≫ (originalFamilyNativeIso B hZ K hK T F hbaseF g hF).inv.baseMap = _
  rw [originalFamilyNativeIso_baseMap B hZ K hK U G hbaseG g hG,
    originalFamilyNativeIso_inv_baseMap B hZ K hK T F hbaseF g hF, hδ]
  simp [Category.assoc]

/-- Native fullness constructs a unique genuine original Cartesian arrow,
with exact recovery of its native total map and its original coefficient map. -/
theorem existsUnique_original_cartesian_map (a : U ⟶ T) (δ : G ⟶ F)
    (hδ : δ.baseMap = eqToHom hbaseG ≫
      (Over.map (fieldToInteger B hZ K hK)).map a ≫ eqToHom hbaseF.symm) :
    ∃! r : (originalFamily B hZ K hK U G hbaseG g hG).total.obj ⟶
        (originalFamily B hZ K hK T F hbaseF g hF).total.obj,
      IsPullback r (originalFamily B hZ K hK U G hbaseG g hG).projection
        (originalFamily B hZ K hK T F hbaseF g hF).projection
        (yoneda.map ((boundedInclusion B K hK).map a)) ∧
      nativeTotalMap B hZ K hK
          (originalFamily B hZ K hK T F hbaseF g hF)
          (originalFamily B hZ K hK U G hbaseG g hG) r =
        (comparisonArrow B hZ K hK T U F G hbaseF hbaseG g hF hG δ).totalMap :=
  AllTestNativeFamilyFull.existsUnique_original_cartesian_lift B hZ K hK a
    (originalFamily B hZ K hK T F hbaseF g hF)
    (originalFamily B hZ K hK U G hbaseG g hG)
    (comparisonArrow B hZ K hK T U F G hbaseF hbaseG g hF hG δ)
    (comparisonArrow_baseMap B hZ K hK T U F G hbaseF hbaseG g hF hG a δ hδ)

/-- The constructed full-original total map, not a supplied lift. -/
def originalCartesianMap (a : U ⟶ T) (δ : G ⟶ F)
    (hδ : δ.baseMap = eqToHom hbaseG ≫
      (Over.map (fieldToInteger B hZ K hK)).map a ≫ eqToHom hbaseF.symm) :
    (originalFamily B hZ K hK U G hbaseG g hG).total.obj ⟶
      (originalFamily B hZ K hK T F hbaseF g hF).total.obj :=
  (existsUnique_original_cartesian_map B hZ K hK T U F G hbaseF hbaseG g hF hG a δ hδ).choose

/-- The actual Cartesian square holds on all original test schemes. -/
theorem originalCartesianMap_isPullback (a : U ⟶ T) (δ : G ⟶ F)
    (hδ : δ.baseMap = eqToHom hbaseG ≫
      (Over.map (fieldToInteger B hZ K hK)).map a ≫ eqToHom hbaseF.symm) :
    IsPullback (originalCartesianMap B hZ K hK T U F G hbaseF hbaseG g hF hG a δ hδ)
      (originalFamily B hZ K hK U G hbaseG g hG).projection
      (originalFamily B hZ K hK T F hbaseF g hF).projection
      (yoneda.map ((boundedInclusion B K hK).map a)) :=
  (existsUnique_original_cartesian_map B hZ K hK T U F G hbaseF hbaseG g hF hG a δ hδ).choose_spec.1.1

/-- The same constructed map recovers the actual given native arrow. -/
theorem originalCartesianMap_nativeTotalMap (a : U ⟶ T) (δ : G ⟶ F)
    (hδ : δ.baseMap = eqToHom hbaseG ≫
      (Over.map (fieldToInteger B hZ K hK)).map a ≫ eqToHom hbaseF.symm) :
    nativeTotalMap B hZ K hK
        (originalFamily B hZ K hK T F hbaseF g hF)
        (originalFamily B hZ K hK U G hbaseG g hG)
        (originalCartesianMap B hZ K hK T U F G hbaseF hbaseG g hF hG a δ hδ) =
      (comparisonArrow B hZ K hK T U F G hbaseF hbaseG g hF hG δ).totalMap :=
  (existsUnique_original_cartesian_map B hZ K hK T U F G hbaseF hbaseG g hF hG a δ hδ).choose_spec.1.2

end M9StacksIntegration.AllTestNativeOriginalFamilyNaturality

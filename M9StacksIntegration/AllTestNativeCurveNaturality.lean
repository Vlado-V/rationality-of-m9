module

public import M9StacksIntegration.AllTestNativeCurveFamily

/-!
# Actual cartesian naturality of the original-to-native family construction

Every original full all-test cartesian square gives an actual morphism of
native curve families. Restriction, the actual representable comparison and
the actual lower-shriek extension transport the square. The underlying base
map retains the original map over Spec K; no field automorphisms, full
faithfulness, or classification premise is inserted.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeCurveNaturality
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestNativeCurveFamily
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The actual native map of total spaces induced by an original map. -/
def nativeTotalMap {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj) :
    nativeTotal B hZ K hK G ⟶ nativeTotal B hZ K hK F :=
  ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor
    (fieldToInteger B hZ K hK)).map (restrictMap K B hK r))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every full original cartesian square remains cartesian after the actual
native family construction, on the entire native site. -/
theorem native_cartesian {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (h : IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map a))) :
    IsPullback (nativeTotalMap B hZ K hK F G r)
      (nativeCurveFamily B hZ K hK G).toBase (nativeCurveFamily B hZ K hK F).toBase
      (schemeSpaceMap ((Over.map (fieldToInteger B hZ K hK)).map a)) := by
  have hr : IsPullback (restrictMap K B hK r)
      (baseMap K B hK U G.projection) (baseMap K B hK T F.projection) (yoneda.map a) := by
    apply (restrict_isPullback K B hK h).of_iso (Iso.refl _) (Iso.refl _)
      (restrictRepresentableIso B K hK U) (restrictRepresentableIso B K hK T)
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, baseMap, Category.id_comp]
    · simp only [Iso.refl_hom, baseMap, Category.id_comp]
    · exact restrictRepresentableIso_naturality K B hK a
  let k := fieldToInteger B hZ K hK
  let L := OverShriek.relocalizePresheafFunctor k
  have hi : IsPullback (L.map (restrictMap K B hK r))
      (nativeProjection B hZ K hK G).hom (nativeProjection B hZ K hK F).hom
      (yoneda.map ((Over.map k).map a)) := by
    apply (hr.map L).of_iso (Iso.refl _) (Iso.refl _)
      (relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k U)
      (relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k T)
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, nativeProjection,
        AllTestNativeCartesianCover.extendedProjection, Category.id_comp] <;> rfl
    · simp only [Iso.refl_hom, nativeProjection,
        AllTestNativeCartesianCover.extendedProjection, Category.id_comp] <;> rfl
    · exact relocalizedYonedaIso_naturality B (B.obj hK) (B.obj hZ) k a
  exact IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B integerBase hZ)) hi

/-- The actual morphism of native curve families from an original full
cartesian square. This is exactly the arrow data required by a classifier's
naturality condition. -/
def nativeCartesianMap {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (h : IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map a))) :
    nativeCurveFamily B hZ K hK G ⟶ nativeCurveFamily B hZ K hK F :=
  { baseMap := (Over.map (fieldToInteger B hZ K hK)).map a
    totalMap := nativeTotalMap B hZ K hK F G r
    cartesian := native_cartesian B hZ K hK a F G r h }

/-- The constructed native arrow retains the actual original base map. -/
@[simp] theorem nativeCartesianMap_base_toScheme
    {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ} (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (h : IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map a))) :
    (BigFppfOver.toScheme B integerBase hZ).map
        (nativeCartesianMap B hZ K hK a F G r h).baseMap =
      ((boundedInclusion B K hK).map a).left := rfl

/-- The same native arrow commutes with the ORIGINAL coefficient map. -/
theorem nativeCartesianMap_coefficient
    {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ} (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (h : IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map a))) :
    (nativeCartesianMap B hZ K hK a F G r h).baseMap ≫ baseCoefficientMap B hZ K hK T =
      baseCoefficientMap B hZ K hK U := by
  apply Over.OverMorphism.ext
  exact Over.w a

end M9StacksIntegration.AllTestNativeCurveNaturality

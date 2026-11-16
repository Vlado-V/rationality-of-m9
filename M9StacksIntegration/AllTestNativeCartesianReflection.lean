module

public import M9StacksIntegration.AllTestRelocalizeReflection
public import M9StacksIntegration.AllTestBoundedCartesianReflection
public import M9StacksIntegration.AllTestNativeCurveNaturality

/-!
# Reflection of genuine native family squares to the full original category

Actual lower-shriek conservativity reflects the first cartesian square.
The actual Yoneda comparisons identify the base schemes. The proved
bounded K-site cartesian reflection then yields the square on EVERY
original test scheme, without an assumed comparison equivalence.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeCartesianReflection
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestNativeCurveFamily AllTestNativeCurveNaturality AllTestNativeCartesianCover
  AllTestBoundedCartesianReflection AllTestRelocalizeReflection
universe u

private theorem inverse_naturality {D : Type*} [Category D]
    {X Y X' Y' : D} (e : X ≅ X') (f : Y ≅ Y') (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : a ≫ f.hom = e.hom ≫ b) : b ≫ f.inv = e.inv ≫ a := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cartesian square of the genuine native curve-family images is already
cartesian on the entire unchanged original test category. -/
theorem original_cartesian_of_native_cartesian
    {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj)
    (h : IsPullback (nativeTotalMap B hZ K hK F G r)
      (nativeCurveFamily B hZ K hK G).toBase (nativeCurveFamily B hZ K hK F).toBase
      (schemeSpaceMap ((Over.map (fieldToInteger B hZ K hK)).map a))) :
    IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map a)) := by
  let k := fieldToInteger B hZ K hK
  let L := OverShriek.relocalizePresheafFunctor k
  let eU := relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k U
  let eT := relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k T
  have hi := h.map (ObjectProperty.ι (IsAlgebraicSpace B integerBase hZ))
  change IsPullback (L.map (restrictMap K B hK r))
    (nativeProjection B hZ K hK G).hom (nativeProjection B hZ K hK F).hom
    (yoneda.map ((Over.map k).map a)) at hi
  have hL : IsPullback (L.map (restrictMap K B hK r))
      (L.map (baseMap K B hK U G.projection))
      (L.map (baseMap K B hK T F.projection)) (L.map (yoneda.map a)) := by
    apply hi.of_iso (Iso.refl _) (Iso.refl _) eU.symm eT.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · change (L.map (baseMap K B hK U G.projection) ≫ eU.hom) ≫ eU.inv =
        𝟙 _ ≫ L.map (baseMap K B hK U G.projection)
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · change (L.map (baseMap K B hK T F.projection) ≫ eT.hom) ≫ eT.inv =
        𝟙 _ ≫ L.map (baseMap K B hK T F.projection)
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · exact inverse_naturality eU eT (L.map (yoneda.map a))
        (yoneda.map ((Over.map k).map a))
        (relocalizedYonedaIso_naturality B (B.obj hK) (B.obj hZ) k a)
  have hr := isPullback_of_relocalize_isPullback k hL
  have hraw : IsPullback (restrictMap K B hK r) (restrictMap K B hK G.projection)
      (restrictMap K B hK F.projection)
      (restrictMap K B hK (yoneda.map ((boundedInclusion B K hK).map a))) := by
    apply hr.of_iso (Iso.refl _) (Iso.refl _)
      (restrictRepresentableIso B K hK U).symm (restrictRepresentableIso B K hK T).symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.symm_hom, Iso.refl_hom, baseMap, Category.assoc, Iso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · simp only [Iso.symm_hom, Iso.refl_hom, baseMap, Category.assoc, Iso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · exact inverse_naturality (restrictRepresentableIso B K hK U)
        (restrictRepresentableIso B K hK T)
        (restrictMap K B hK (yoneda.map ((boundedInclusion B K hK).map a))) (yoneda.map a)
        (restrictRepresentableIso_naturality K B hK a)
  exact isPullback_of_restrict_isPullback K B hK F G a r hraw

/-- The genuine native square and the full original square agree, both ways. -/
theorem native_cartesian_iff_original
    {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (r : G.total.obj ⟶ F.total.obj) :
    IsPullback (nativeTotalMap B hZ K hK F G r)
      (nativeCurveFamily B hZ K hK G).toBase (nativeCurveFamily B hZ K hK F).toBase
      (schemeSpaceMap ((Over.map (fieldToInteger B hZ K hK)).map a)) ↔
    IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map a)) :=
  ⟨original_cartesian_of_native_cartesian B hZ K hK a F G r,
    native_cartesian B hZ K hK a F G r⟩

end M9StacksIntegration.AllTestNativeCartesianReflection

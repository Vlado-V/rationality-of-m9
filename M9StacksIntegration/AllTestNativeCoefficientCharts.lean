module

public import M9StacksIntegration.AllTestNativeCoefficientProjection
public import M9StacksIntegration.AllTestNativeCartesianCover

/-!
# Actual coefficient-preserving schematic charts

A schematic Cartesian chart of a native space with its ORIGINAL projection
has a uniquely determined chart over the ORIGINAL coefficient base. The
map is constructed from the actual pointed relocalization equivalence.
The actual relocalization square then proves its full Cartesian property;
no desired chart map, comparison, or fullness is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeCoefficientCharts
open AllTestNativeCoefficientProjection AllTestNativeCoefficientSpace
  AllTestPointedRelocalizeFull AllTestRelocalizeReflection
universe u
variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- Actual scheme maps retain the ORIGINAL represented coefficient map. -/
theorem map_baseCoefficientMap {U T : BigFppfOver B S hS} (a : U ⟶ T) :
    (Over.map k).map a ≫ baseCoefficientMap B S S' hS hS' k T =
      baseCoefficientMap B S S' hS hS' k U := by
  apply Over.OverMorphism.ext
  exact Over.w a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The ACTUAL native square supplies a unique coefficient-preserving chart.
All displayed maps and bases are the original ones. -/
theorem existsUnique_chartMap
    {X : AlgebraicSpaces B S' hS'}
    {Z U T : BigFppfOver B S hS}
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T))
    (q : Z ⟶ U) (v : U ⟶ T)
    (p : yoneda.obj ((Over.map k).obj Z) ⟶ X.obj)
    (hcart : IsPullback p (yoneda.map ((Over.map k).map q))
      π (yoneda.map ((Over.map k).map v))) :
    ∃! r : yoneda.obj Z ⟶ (projectionSpace B S S' hS hS' k T π).obj,
      (OverShriek.relocalizePresheafFunctor k).map r ≫
        (coefficientRelocalizeIso B S S' hS hS' k X
          (projectionCoefficient B S S' hS hS' k T π)).hom =
      (relocalizedYonedaIso B (B.obj hS) (B.obj hS') k Z).hom ≫ p := by
  let L := OverShriek.relocalizePresheafFunctor k
  let H := projectionSpace B S S' hS hS' k T π
  let c := projectionCoefficient B S S' hS hS' k T π
  let eX := coefficientRelocalizeIso B S S' hS hS' k X c
  let eZ := relocalizedYonedaIso B (B.obj hS) (B.obj hS') k Z
  have hc : p ≫ c = yoneda.map (baseCoefficientMap B S S' hS hS' k Z) := by
    change p ≫ (π ≫ yoneda.map (baseCoefficientMap B S S' hS hS' k T)) = _
    rw [← Category.assoc, hcart.w, Category.assoc,
      ← (yoneda (C := BigFppfOver B S' hS')).map_comp,
      map_baseCoefficientMap, ← (yoneda (C := BigFppfOver B S' hS')).map_comp,
      map_baseCoefficientMap]
  have hstruct : eX.inv ≫ OverShriek.relocalizeToYoneda k H.obj = c := by
    rw [← coefficientRelocalizeIso_toYoneda B S S' hS hS' k X c]
    exact Iso.inv_hom_id_assoc eX c
  let f := eZ.hom ≫ p ≫ eX.inv
  have hf : f ≫ OverShriek.relocalizeToYoneda k H.obj =
      OverShriek.relocalizeToYoneda k (yoneda.obj Z) := by
    change (eZ.hom ≫ p ≫ eX.inv) ≫ _ = _
    rw [Category.assoc, Category.assoc, hstruct, hc]
    exact relocalizedYonedaIso_toYoneda B S S' hS hS' k Z
  obtain ⟨r, hr, huniq⟩ := existsUnique_preimage_of_pointed B S S' hS hS' k f hf
  have hr' : L.map r ≫ eX.hom = eZ.hom ≫ p := by
    rw [hr]
    change (eZ.hom ≫ p ≫ eX.inv) ≫ eX.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨r, hr', ?_⟩
  intro r' hr''
  apply huniq r'
  apply (cancel_mono eX.hom).mp
  exact (hr''.trans hr'.symm).trans (congrArg (fun m => m ≫ eX.hom) hr)

/-- The actual coefficient-base chart obtained above. -/
def chartMap
    {X : AlgebraicSpaces B S' hS'}
    {Z U T : BigFppfOver B S hS}
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T))
    (q : Z ⟶ U) (v : U ⟶ T)
    (p : yoneda.obj ((Over.map k).obj Z) ⟶ X.obj)
    (hcart : IsPullback p (yoneda.map ((Over.map k).map q))
      π (yoneda.map ((Over.map k).map v))) :
    yoneda.obj Z ⟶ (projectionSpace B S S' hS hS' k T π).obj :=
  (existsUnique_chartMap B S S' hS hS' k π q v p hcart).choose

/-- Literal recovery of the ORIGINAL native chart. -/
theorem chartMap_relocalize
    {X : AlgebraicSpaces B S' hS'}
    {Z U T : BigFppfOver B S hS}
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T))
    (q : Z ⟶ U) (v : U ⟶ T)
    (p : yoneda.obj ((Over.map k).obj Z) ⟶ X.obj)
    (hcart : IsPullback p (yoneda.map ((Over.map k).map q))
      π (yoneda.map ((Over.map k).map v))) :
    (OverShriek.relocalizePresheafFunctor k).map
        (chartMap B S S' hS hS' k π q v p hcart) ≫
      (coefficientRelocalizeIso B S S' hS hS' k X
        (projectionCoefficient B S S' hS hS' k T π)).hom =
      (relocalizedYonedaIso B (B.obj hS) (B.obj hS') k Z).hom ≫ p :=
  (existsUnique_chartMap B S S' hS hS' k π q v p hcart).choose_spec.1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual lifted chart has its genuine full Cartesian universal property. -/
theorem chartMap_isPullback
    {X : AlgebraicSpaces B S' hS'}
    {Z U T : BigFppfOver B S hS}
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T))
    (q : Z ⟶ U) (v : U ⟶ T)
    (p : yoneda.obj ((Over.map k).obj Z) ⟶ X.obj)
    (hcart : IsPullback p (yoneda.map ((Over.map k).map q))
      π (yoneda.map ((Over.map k).map v))) :
    IsPullback (chartMap B S S' hS hS' k π q v p hcart) (yoneda.map q)
      (nativeProjection B S S' hS hS' k T π).hom (yoneda.map v) := by
  apply isPullback_of_relocalize_isPullback k
  let eZ := relocalizedYonedaIso B (B.obj hS) (B.obj hS') k Z
  let eU := relocalizedYonedaIso B (B.obj hS) (B.obj hS') k U
  let eT := relocalizedYonedaIso B (B.obj hS) (B.obj hS') k T
  let eX := coefficientRelocalizeIso B S S' hS hS' k X
    (projectionCoefficient B S S' hS hS' k T π)
  apply hcart.of_iso' eZ eX eU eT
  · exact (chartMap_relocalize B S S' hS hS' k π q v p hcart).symm
  · exact (relocalizedYonedaIso_naturality B (B.obj hS) (B.obj hS') k q).symm
  · exact (nativeProjection_relocalize B S S' hS hS' k T π).symm
  · exact (relocalizedYonedaIso_naturality B (B.obj hS) (B.obj hS') k v).symm

end M9StacksIntegration.AllTestNativeCoefficientCharts

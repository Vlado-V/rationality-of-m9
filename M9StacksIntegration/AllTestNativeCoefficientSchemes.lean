module

public import M9StacksIntegration.AllTestNativeCoefficientProjection

/-!
# SAME schemes with their ORIGINAL coefficient structure

An actual map U → T with T over S supplies U an actual S-structure.
Forgetting S again recovers precisely the original U by the identity of
underlying schemes. Actual maps and Cartesian squares are retained.
This is relative to the original coefficient map S → S'; no finite-type
condition over Spec Z or replacement of the coefficient field occurs.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeCoefficientSchemes
universe u
variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- The SAME scheme U with the actual S-structure supplied by U → T → S. -/
abbrev schemeLift {T : BigFppfOver B S hS} {U : BigFppfOver B S' hS'}
    (a : U ⟶ (Over.map k).obj T) : BigFppfOver B S hS :=
  Over.mk (a.left ≫ T.hom)

/-- Forgetting the newly recorded coefficient structure recovers U by the
IDENTITY of its underlying original scheme. -/
def schemeLiftIso {T : BigFppfOver B S hS} {U : BigFppfOver B S' hS'}
    (a : U ⟶ (Over.map k).obj T) :
    (Over.map k).obj (schemeLift B S S' hS hS' k a) ≅ U :=
  Over.isoMk (Iso.refl U.left) (by
    change 𝟙 U.left ≫ U.hom = (a.left ≫ T.hom) ≫ k
    rw [Category.id_comp, Category.assoc]
    exact (Over.w a).symm)

/-- The actual U → T map over the ORIGINAL coefficient base. -/
def schemeLiftBaseMap {T : BigFppfOver B S hS} {U : BigFppfOver B S' hS'}
    (a : U ⟶ (Over.map k).obj T) : schemeLift B S S' hS hS' k a ⟶ T :=
  Over.homMk a.left rfl

/-- Every actual Z → U chart map retains the SAME underlying scheme map. -/
def schemeLiftMap {T : BigFppfOver B S hS} {U Z : BigFppfOver B S' hS'}
    (a : U ⟶ (Over.map k).obj T) (q : Z ⟶ U) :
    schemeLift B S S' hS hS' k (q ≫ a) ⟶ schemeLift B S S' hS hS' k a :=
  Over.homMk q.left (Category.assoc q.left a.left T.hom).symm

/-- Literal compatibility of the base map with forgetting coefficients. -/
theorem schemeLiftBaseMap_comm {T : BigFppfOver B S hS} {U : BigFppfOver B S' hS'}
    (a : U ⟶ (Over.map k).obj T) :
    (Over.map k).map (schemeLiftBaseMap B S S' hS hS' k a) =
      (schemeLiftIso B S S' hS hS' k a).hom ≫ a := by
  apply Over.OverMorphism.ext
  change a.left = 𝟙 U.left ≫ a.left
  exact (Category.id_comp a.left).symm

/-- Literal compatibility of the chart map with forgetting coefficients. -/
theorem schemeLiftMap_comm {T : BigFppfOver B S hS} {U Z : BigFppfOver B S' hS'}
    (a : U ⟶ (Over.map k).obj T) (q : Z ⟶ U) :
    (Over.map k).map (schemeLiftMap B S S' hS hS' k a q) ≫
        (schemeLiftIso B S S' hS hS' k a).hom =
      (schemeLiftIso B S S' hS hS' k (q ≫ a)).hom ≫ q := by
  apply Over.OverMorphism.ext
  change q.left ≫ 𝟙 U.left = 𝟙 Z.left ≫ q.left
  simp only [Category.comp_id, Category.id_comp]

/-- The underlying ORIGINAL chart map is literally unchanged. -/
@[simp] theorem schemeLiftMap_toScheme {T : BigFppfOver B S hS}
    {U Z : BigFppfOver B S' hS'} (a : U ⟶ (Over.map k).obj T) (q : Z ⟶ U) :
    (BigFppfOver.toScheme B S hS).map (schemeLiftMap B S S' hS hS' k a q) =
      (BigFppfOver.toScheme B S' hS').map q := rfl

/-- The underlying ORIGINAL base-cover map is literally unchanged. -/
@[simp] theorem schemeLiftBaseMap_toScheme {T : BigFppfOver B S hS}
    {U : BigFppfOver B S' hS'} (a : U ⟶ (Over.map k).obj T) :
    (BigFppfOver.toScheme B S hS).map (schemeLiftBaseMap B S S' hS hS' k a) =
      (BigFppfOver.toScheme B S' hS').map a := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An ACTUAL native schematic chart, including its entire Cartesian square,
retains the SAME original schemes after recording their coefficient maps. -/
theorem schemeLift_chart_isPullback
    {X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} {U Z : BigFppfOver B S' hS'}
    (π : X ⟶ yoneda.obj ((Over.map k).obj T))
    (a : U ⟶ (Over.map k).obj T) (q : Z ⟶ U)
    (p : yoneda.obj Z ⟶ X)
    (hcart : IsPullback p (yoneda.map q) π (yoneda.map a)) :
    IsPullback
      (yoneda.map (schemeLiftIso B S S' hS hS' k (q ≫ a)).hom ≫ p)
      (yoneda.map ((Over.map k).map (schemeLiftMap B S S' hS hS' k a q)))
      π (yoneda.map ((Over.map k).map (schemeLiftBaseMap B S S' hS hS' k a))) := by
  apply hcart.of_iso'
    ((yoneda (C := BigFppfOver B S' hS')).mapIso
      (schemeLiftIso B S S' hS hS' k (q ≫ a)))
    (Iso.refl X)
    ((yoneda (C := BigFppfOver B S' hS')).mapIso
      (schemeLiftIso B S S' hS hS' k a))
    (Iso.refl (yoneda.obj ((Over.map k).obj T)))
  · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
  · simpa only [Functor.mapIso_hom, Functor.map_comp] using
      (congrArg (fun f => (yoneda (C := BigFppfOver B S' hS')).map f)
        (schemeLiftMap_comm B S S' hS hS' k a q)).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id,
      Functor.map_comp] using
      (congrArg (fun f => (yoneda (C := BigFppfOver B S' hS')).map f)
        (schemeLiftBaseMap_comm B S S' hS hS' k a)).symm

end M9StacksIntegration.AllTestNativeCoefficientSchemes

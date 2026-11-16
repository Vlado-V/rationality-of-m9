module

public import M9StacksIntegration.AllTestNativeCoefficientSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension

/-!
# Actual inverse coefficient-base projection

A genuine map X → T, with T over S, supplies X its ORIGINAL S-structure.
The actual coefficient-space inverse constructs the actual algebraic space
over S and the unique actual map to the SAME represented T. Relocalizing
that projection recovers the ORIGINAL native projection. This supplies the
projection data for reverse native curve-family construction, without
assuming its as-yet separate all-field cohomological family condition.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeCoefficientProjection
open AllTestNativeCoefficientSpace AllTestPointedRelocalizeFull
universe u
variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- The SAME represented base scheme remembers its ORIGINAL S-structure. -/
abbrev baseCoefficientMap (T : BigFppfOver B S hS) : (Over.map k).obj T ⟶ Over.mk k :=
  Over.homMk T.hom rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual Yoneda relocalization retains its ORIGINAL coefficient map. -/
theorem relocalizedYonedaIso_toYoneda (T : BigFppfOver B S hS) :
    (relocalizedYonedaIso B (B.obj hS) (B.obj hS') k T).hom ≫
        yoneda.map (baseCoefficientMap B S S' hS hS' k T) =
      OverShriek.relocalizeToYoneda k (yoneda.obj T) := by
  ext W x
  rcases x with ⟨⟨ψ, s⟩, hψ⟩
  apply Over.OverMorphism.ext
  exact Over.w s

/-- The actual S-structure supplied by the actual projection to T. -/
abbrev projectionCoefficient {X : AlgebraicSpaces B S' hS'}
    (T : BigFppfOver B S hS) (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    X.obj ⟶ yoneda.obj (Over.mk k) :=
  π ≫ yoneda.map (baseCoefficientMap B S S' hS hS' k T)

/-- The actual algebraic space over the ORIGINAL coefficient base. -/
abbrev projectionSpace {X : AlgebraicSpaces B S' hS'}
    (T : BigFppfOver B S hS) (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    AlgebraicSpaces B S hS :=
  coefficientSpace B S S' hS hS' k X (projectionCoefficient B S S' hS hS' k T π)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A unique actual projection over S, whose relocalization is the ORIGINAL
native projection. No projection/comparison inverse is assumed. -/
theorem existsUnique_projection {X : AlgebraicSpaces B S' hS'}
    (T : BigFppfOver B S hS) (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    ∃! r : (projectionSpace B S S' hS hS' k T π).obj ⟶ yoneda.obj T,
      (OverShriek.relocalizePresheafFunctor k).map r ≫
          (relocalizedYonedaIso B (B.obj hS) (B.obj hS') k T).hom =
        (coefficientRelocalizeIso B S S' hS hS' k X
          (projectionCoefficient B S S' hS hS' k T π)).hom ≫ π := by
  let L := OverShriek.relocalizePresheafFunctor k
  let H := projectionSpace B S S' hS hS' k T π
  let eT := relocalizedYonedaIso B (B.obj hS) (B.obj hS') k T
  let eX := coefficientRelocalizeIso B S S' hS hS' k X
    (projectionCoefficient B S S' hS hS' k T π)
  let f := eX.hom ≫ π ≫ eT.inv
  have hstruct : eT.inv ≫ OverShriek.relocalizeToYoneda k (yoneda.obj T) =
      yoneda.map (baseCoefficientMap B S S' hS hS' k T) := by
    calc
      eT.inv ≫ OverShriek.relocalizeToYoneda k (yoneda.obj T) =
          eT.inv ≫ (eT.hom ≫ yoneda.map (baseCoefficientMap B S S' hS hS' k T)) :=
        congrArg (fun m => eT.inv ≫ m) (relocalizedYonedaIso_toYoneda B S S' hS hS' k T).symm
      _ = yoneda.map (baseCoefficientMap B S S' hS hS' k T) := Iso.inv_hom_id_assoc eT _
  have hf : f ≫ OverShriek.relocalizeToYoneda k (yoneda.obj T) =
      OverShriek.relocalizeToYoneda k H.obj := by
    calc
      f ≫ OverShriek.relocalizeToYoneda k (yoneda.obj T) =
          (eX.hom ≫ π) ≫ (eT.inv ≫ OverShriek.relocalizeToYoneda k (yoneda.obj T)) := by
        simp only [f, Category.assoc]
      _ = (eX.hom ≫ π) ≫ yoneda.map (baseCoefficientMap B S S' hS hS' k T) :=
        congrArg (fun m => (eX.hom ≫ π) ≫ m) hstruct
      _ = eX.hom ≫ projectionCoefficient B S S' hS hS' k T π := Category.assoc _ _ _
      _ = OverShriek.relocalizeToYoneda k H.obj :=
        coefficientRelocalizeIso_toYoneda B S S' hS hS' k X _
  obtain ⟨r, hr, huniq⟩ := existsUnique_preimage_of_pointed B S S' hS hS' k f hf
  have hr' : L.map r ≫ eT.hom = eX.hom ≫ π := by
    rw [hr]
    change (eX.hom ≫ π ≫ eT.inv) ≫ eT.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨r, hr', ?_⟩
  intro r' hr''
  apply huniq r'
  apply (cancel_mono eT.hom).mp
  exact (hr''.trans hr'.symm).trans (congrArg (fun m => m ≫ eT.hom) hr)

/-- The actual native coefficient-base projection, as an algebraic-space map. -/
def nativeProjection {X : AlgebraicSpaces B S' hS'}
    (T : BigFppfOver B S hS) (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    projectionSpace B S S' hS hS' k T π ⟶ schemeSpace T :=
  ObjectProperty.homMk (existsUnique_projection B S S' hS hS' k T π).choose

/-- The chosen actual projection has the proved actual original comparison. -/
theorem nativeProjection_relocalize {X : AlgebraicSpaces B S' hS'}
    (T : BigFppfOver B S hS) (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    (OverShriek.relocalizePresheafFunctor k).map
        (nativeProjection B S S' hS hS' k T π).hom ≫
        (relocalizedYonedaIso B (B.obj hS) (B.obj hS') k T).hom =
      (coefficientRelocalizeIso B S S' hS hS' k X
        (projectionCoefficient B S S' hS hS' k T π)).hom ≫ π :=
  (existsUnique_projection B S S' hS hS' k T π).choose_spec.1

end M9StacksIntegration.AllTestNativeCoefficientProjection

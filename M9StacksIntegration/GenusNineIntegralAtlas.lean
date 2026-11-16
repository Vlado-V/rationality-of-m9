module

public import M9StacksIntegration.GenusNineStackSmooth
public import M9StacksIntegration.GenusNineStackQuasiCompact
public import M9StacksIntegration.SmoothStackIntegralAtlas

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

attribute [local instance 1100] AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine
  AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated

@[expose] public section

/-! Integral smooth charts of the actual native genus-nine stack.
Source smoothness and quasi-compactness come from the independent genuine
native producers. All atlas properties and integral open components are
conclusions, with no integrality, irreducibility, density, or chosen-atlas
premise on M9.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory

namespace M9Native.GenusNineIntegralAtlas

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The unchanged actual native stack of smooth genus-nine curves over K. -/
abbrev sourceStack :=
  M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)

/-- An actual affine atlas, with structural smoothness derived from the
genuine source smoothness and native boundedness theorems. -/
theorem exists_atlas :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK)
      (a : Stack.schemeStack B (Spec (.of K)) hK U ⟶ sourceStack B hZ K hK),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) ∧
      Stack.IsSurjective B (Spec (.of K)) hK a ∧
      Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK a ∧
      Smooth (B.inclusion.map U.hom) :=
  SmoothStackIntegralAtlas.exists_affine_smooth_atlas B K hK (sourceStack B hZ K hK)
    (GenusNineStackSmooth.smooth B hZ K hK 9 (by decide))
    (GenusNineStackQuasiCompact.quasiCompact B hZ K hK 9 (by decide))

/-- The selected native affine atlas base. -/
def atlasBase : BigFppfOver B (Spec (.of K)) hK := (exists_atlas B hZ K hK).choose

/-- Its original underlying scheme. -/
abbrev atlasScheme :=
  (BigFppfOver.toScheme B (Spec (.of K)) hK).obj (atlasBase B hZ K hK)

/-- The selected actual smooth surjective map to the original source. -/
def atlasMap : Stack.schemeStack B (Spec (.of K)) hK (atlasBase B hZ K hK) ⟶
    sourceStack B hZ K hK := (exists_atlas B hZ K hK).choose_spec.choose

theorem atlas_affine : IsAffine (atlasScheme B hZ K hK) :=
  (exists_atlas B hZ K hK).choose_spec.choose_spec.1

theorem atlas_surjective : Stack.IsSurjective B (Spec (.of K)) hK (atlasMap B hZ K hK) :=
  (exists_atlas B hZ K hK).choose_spec.choose_spec.2.1

theorem atlas_smooth :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK (atlasMap B hZ K hK) :=
  (exists_atlas B hZ K hK).choose_spec.choose_spec.2.2.1

theorem atlas_structural_smooth : Smooth (B.inclusion.map (atlasBase B hZ K hK).hom) :=
  (exists_atlas B hZ K hK).choose_spec.choose_spec.2.2.2

/-- An actual integral open component of the selected atlas scheme. -/
def componentOpen (x : atlasScheme B hZ K hK) : (atlasScheme B hZ K hK).Opens :=
  let _ := atlas_structural_smooth B hZ K hK
  SmoothIntegralComponentCover.componentOpen (B.inclusion.map (atlasBase B hZ K hK).hom) x

/-- The same original component is an object in the same native field site. -/
def componentSite (x : atlasScheme B hZ K hK) : BigFppfOver B (Spec (.of K)) hK :=
  SmoothStackIntegralAtlas.openSite B (Spec (.of K)) hK (atlasBase B hZ K hK)
    (componentOpen B hZ K hK x)

/-- Its actual restricted atlas map to the native genus-nine source. -/
def componentMap (x : atlasScheme B hZ K hK) :
    Stack.schemeStack B (Spec (.of K)) hK (componentSite B hZ K hK x) ⟶
      sourceStack B hZ K hK :=
  SmoothStackIntegralAtlas.openAtlasMap B (Spec (.of K)) hK (atlasMap B hZ K hK)
    (componentOpen B hZ K hK x)

theorem component_integral (x : atlasScheme B hZ K hK) :
    IsIntegral (componentOpen B hZ K hK x).toScheme := by
  let _ := atlas_structural_smooth B hZ K hK
  exact SmoothIntegralComponentCover.component_integral
    (B.inclusion.map (atlasBase B hZ K hK).hom) x

theorem component_smooth (x : atlasScheme B hZ K hK) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK (componentMap B hZ K hK x) :=
  SmoothStackIntegralAtlas.openAtlasMap_smooth B (Spec (.of K)) hK
    (atlasMap B hZ K hK) (atlas_smooth B hZ K hK) _

theorem component_structural_properties (x : atlasScheme B hZ K hK) :
    Smooth (B.inclusion.map (componentSite B hZ K hK x).hom) ∧
      QuasiCompact (B.inclusion.map (componentSite B hZ K hK x).hom) ∧
      LocallyOfFiniteType (B.inclusion.map (componentSite B hZ K hK x).hom) := by
  let _ := atlas_structural_smooth B hZ K hK
  let _ : IsAffine (B.inclusion.obj (atlasBase B hZ K hK).left) := atlas_affine B hZ K hK
  let _ : CompactSpace (B.inclusion.obj (atlasBase B hZ K hK).left) := inferInstance
  have h := SmoothIntegralComponentCover.component_finiteType
    (B.inclusion.map (atlasBase B hZ K hK).hom) x
  exact ⟨SmoothIntegralComponentCover.component_smooth _ x, h.1, h.2⟩

/-- The component's structural map is separated, since it is an open
subscheme of the same actual affine atlas. -/
theorem component_structural_separated (x : atlasScheme B hZ K hK) :
    IsSeparated (B.inclusion.map (componentSite B hZ K hK x).hom) := by
  let _ : IsAffine (B.inclusion.obj (atlasBase B hZ K hK).left) := atlas_affine B hZ K hK
  let _ : IsSeparated (B.inclusion.map (atlasBase B hZ K hK).hom) := inferInstance
  change IsSeparated ((componentOpen B hZ K hK x).ι ≫
    B.inclusion.map (atlasBase B hZ K hK).hom)
  infer_instance

/-- Finitely many actual integral smooth chart components cover every
native point of the actual smooth genus-nine stack. -/
theorem exists_finite_component_cover :
    ∃ t : Finset (atlasScheme B hZ K hK),
      ∀ z : Stack.AlgebraicStacks.points B (Spec (.of K)) hK (sourceStack B hZ K hK),
        ∃ y ∈ t, z ∈ Set.range
          (SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK
            (componentMap B hZ K hK y)) := by
  let _ := atlas_affine B hZ K hK
  let _ := atlas_structural_smooth B hZ K hK
  obtain ⟨t, -, ht⟩ := SmoothStackIntegralAtlas.finite_integral_component_cover B K hK
    (atlasMap B hZ K hK) (atlas_surjective B hZ K hK) (atlas_smooth B hZ K hK)
  exact ⟨t, ht⟩

end M9Native.GenusNineIntegralAtlas

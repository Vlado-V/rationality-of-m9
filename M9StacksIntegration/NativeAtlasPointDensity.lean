module

public import M9StacksIntegration.SmoothStackIntegralAtlas

/-! Density descends along an actual native chart point-cover.
This supplies only the topological passage from already proved density
on the original component schemes to the native stack point space.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory
attribute [local instance] Stack.reprPointTopology

namespace M9Native.NativeAtlasPointDensity

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The actual native chart point map, read on its original scheme, is
continuous for the native stack point topology. -/
theorem schemePointMap_continuous {X : Stack.AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (a : Stack.schemeStack B S hS U ⟶ X) :
    @Continuous _ _ inferInstance (Stack.pointTopology B S hS X.val)
      (SmoothStackIntegralAtlas.schemePointMap B S hS a) := by
  let _ := Stack.pointTopology B S hS X.val
  exact (Stack.continuous_pointsMap B S hS (Stack.schemeFibredCategory B S hS U) X.val a.hom.hom).comp
    (Stack.pointsHomeomorphScheme B S hS U).symm.continuous

/-- A subset dense after pullback to every member of a genuine chart
point-cover is dense in the native stack. The charts may be the finite
integral open components derived from an actual smooth affine atlas. -/
theorem dense_of_chart_point_cover {X : Stack.AlgebraicStacks.{u, w} B S hS}
    {ι : Type v} (U : ι → BigFppfOver B S hS)
    (a : ∀ i, Stack.schemeStack B S hS (U i) ⟶ X)
    (hcover : ∀ z : Stack.AlgebraicStacks.points B S hS X,
      ∃ i, z ∈ Set.range (SmoothStackIntegralAtlas.schemePointMap B S hS (a i)))
    (D : Set (Stack.AlgebraicStacks.points B S hS X))
    (hdense : ∀ i, Dense ((SmoothStackIntegralAtlas.schemePointMap B S hS (a i)) ⁻¹' D)) :
    @Dense _ (Stack.pointTopology B S hS X.val) D := by
  let _ := Stack.pointTopology B S hS X.val
  intro z
  obtain ⟨i, x, rfl⟩ := hcover z
  exact (schemePointMap_continuous B S hS (a i)).closure_preimage_subset D (hdense i x)

end M9Native.NativeAtlasPointDensity

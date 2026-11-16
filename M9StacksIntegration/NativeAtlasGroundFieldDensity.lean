module

public import M9StacksIntegration.NativeAtlasPointDensity
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! Dense chart opens have dense points over the original algebraically
closed ground field. This retains actual ground-field morphisms and the
literal native chart point, rather than changing a curve's field of definition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u w v

namespace M9Native.NativeAtlasGroundFieldDensity

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The original ground-field points of an actual dense open are dense.
Their structural triangle is literal and their scheme point is retained. -/
theorem dense_groundPoints {V : Scheme.{u}} (s : V ⟶ Spec (.of K))
    [LocallyOfFiniteType s] (U : V.Opens) (hU : Dense (U : Set V)) :
    Dense {x : V | ∃ b : Spec (.of K) ⟶ V,
      b ≫ s = 𝟙 _ ∧ b (IsLocalRing.closedPoint K) = x ∧ x ∈ U} := by
  letI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace s
  have hd : Dense ((U : Set V) ∩ closedPoints V) := by
    rw [dense_iff_closure_eq,
      JacobsonSpace.closure_inter_closedPoints_eq_closure U.isOpen.isLocallyClosed,
      ← dense_iff_closure_eq]
    exact hU
  apply hd.mono
  rintro x ⟨hxU,hx⟩
  exact ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx,
    pointOfClosedPoint_apply s x hx _, hxU⟩

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

/-- Actual ground-field witnesses in a dense chart open give density of
any native point locus containing their actual chart classes. -/
theorem dense_chart_preimage_of_groundPoints
    {X : Stack.AlgebraicStacks.{u,w} B (Spec (.of K)) hK}
    {V : BigFppfOver B (Spec (.of K)) hK}
    (a : Stack.schemeStack B (Spec (.of K)) hK V ⟶ X)
    [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (D : Set (Stack.AlgebraicStacks.points B (Spec (.of K)) hK X))
    (U : ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj V).Opens)
    (hU : Dense (U : Set ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj V)))
    (hmem : ∀ b : Spec (.of K) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj V,
      b ≫ B.inclusion.map V.hom = 𝟙 _ → b (IsLocalRing.closedPoint K) ∈ U →
      SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK a
        (b (IsLocalRing.closedPoint K)) ∈ D) :
    Dense ((SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK a) ⁻¹' D) := by
  apply (dense_groundPoints (B.inclusion.map V.hom) U hU).mono
  rintro x ⟨b,hb,rfl,hx⟩
  exact hmem b hb hx

/-- Density on the original chart schemes descends along their actual
native point cover, with original ground-field representatives retained. -/
theorem dense_of_chart_groundPoint_cover
    {X : Stack.AlgebraicStacks.{u,w} B (Spec (.of K)) hK}
    {ι : Type v} (V : ι → BigFppfOver B (Spec (.of K)) hK)
    (a : ∀ i, Stack.schemeStack B (Spec (.of K)) hK (V i) ⟶ X)
    [∀ i, LocallyOfFiniteType (B.inclusion.map (V i).hom)]
    (hcover : ∀ z : Stack.AlgebraicStacks.points B (Spec (.of K)) hK X,
      ∃ i, z ∈ Set.range (SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK (a i)))
    (D : Set (Stack.AlgebraicStacks.points B (Spec (.of K)) hK X))
    (U : ∀ i, ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj (V i)).Opens)
    (hU : ∀ i, Dense (U i : Set ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj (V i))))
    (hmem : ∀ i (b : Spec (.of K) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj (V i)),
      b ≫ B.inclusion.map (V i).hom = 𝟙 _ → b (IsLocalRing.closedPoint K) ∈ U i →
      SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK (a i)
        (b (IsLocalRing.closedPoint K)) ∈ D) :
    @Dense _ (Stack.pointTopology B (Spec (.of K)) hK X.val) D :=
  NativeAtlasPointDensity.dense_of_chart_point_cover B (Spec (.of K)) hK V a hcover D
    (fun i => dense_chart_preimage_of_groundPoints B hK (a i) D (U i) (hU i) (hmem i))

end M9Native.NativeAtlasGroundFieldDensity
end

module

public import M9StacksIntegration.SmoothIntegralComponentCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition

/-! Finite integral smooth charts from an actual smooth quasi-compact stack.
The affine atlas comes from native quasi-compactness. Its structural
smoothness is transferred through the actual atlas map, and its open
integral components cover the native stack point space.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory
attribute [local instance] Stack.reprPointTopology

namespace M9Native.SmoothStackIntegralAtlas

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An original open subscheme of a native chart, retained in the same site. -/
def openSite (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Over.mk (⟨V.ι ≫ B.inclusion.map U.hom⟩ :
    B.obj (Scheme.size_lt_of_isOpenImmersion V.ι U.left.property) ⟶ B.obj hS)

/-- Its literal original inclusion, as a morphism of the native site. -/
def openSiteInclusion (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : openSite B S hS U V ⟶ U :=
  Over.homMk ⟨V.ι⟩ (by rfl)

/-- The restricted actual stack morphism on the open subscheme. -/
def openAtlasMap {X : Stack.AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (a : Stack.schemeStack B S hS U ⟶ X)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Stack.schemeStack B S hS (openSite B S hS U V) ⟶ X :=
  Stack.schemeStackMap B S hS (openSiteInclusion B S hS U V) ≫ a

/-- Restricting an actual smooth atlas map to an original open preserves
native smoothness. -/
theorem openAtlasMap_smooth {X : Stack.AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (a : Stack.schemeStack B S hS U ⟶ X)
    (ha : Stack.AlgebraicStacks.IsSmooth B S hS a)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Stack.AlgebraicStacks.IsSmooth B S hS (openAtlasMap B S hS a V) :=
  Stack.AlgebraicStacks.isSmooth_comp B S hS _ a
    (Stack.isSmooth_schemeStackMap.{u, w} B S hS (openSiteInclusion B S hS U V)
      (inferInstanceAs (Smooth V.ι))) ha

/-- The point map of an actual stack chart, with its source read on the
original scheme by the native scheme-point homeomorphism. -/
def schemePointMap {X : Stack.AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (a : Stack.schemeStack B S hS U ⟶ X) :
    ((BigFppfOver.toScheme B S hS).obj U) → Stack.AlgebraicStacks.points B S hS X :=
  Stack.AlgebraicStacks.pointsMap B S hS a ∘ (Stack.pointsHomeomorphScheme B S hS U).symm

/-- An open chart's point map retains exactly the same original scheme
point under its original inclusion. -/
theorem schemePointMap_openAtlasMap {X : Stack.AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (a : Stack.schemeStack B S hS U ⟶ X)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) (x : V.toScheme) :
    schemePointMap B S hS (openAtlasMap B S hS a V) x =
      schemePointMap B S hS a (V.ι x) := by
  let z := (Stack.pointsHomeomorphScheme B S hS (openSite B S hS U V)).symm x
  have hz := Stack.pointsHomeomorphScheme_naturality B S hS
    (openSiteInclusion B S hS U V) z
  change Stack.pointsHomeomorphScheme B S hS U
    (Stack.AlgebraicStacks.pointsMap.{u,w} B S hS
      (Stack.schemeStackMap.{u,w} B S hS (openSiteInclusion B S hS U V)) z) =
    V.ι (Stack.pointsHomeomorphScheme B S hS (openSite B S hS U V) z) at hz
  have he : Stack.AlgebraicStacks.pointsMap.{u,w} B S hS
      (Stack.schemeStackMap.{u,w} B S hS (openSiteInclusion B S hS U V)) z =
      (Stack.pointsHomeomorphScheme B S hS U).symm (V.ι x) := by
    apply (Stack.pointsHomeomorphScheme B S hS U).injective
    simpa only [z, Homeomorph.apply_symm_apply] using hz
  change Stack.AlgebraicStacks.pointsMap B S hS (openAtlasMap B S hS a V) z = _
  rw [openAtlasMap, Stack.AlgebraicStacks.pointsMap_comp]
  exact congrArg (Stack.AlgebraicStacks.pointsMap B S hS a) he

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The actual scheme below a smooth chart of a structurally smooth stack
is smooth over the original field. -/
theorem atlas_structural_smooth
    {X : Stack.AlgebraicStacks.{u, w} B (Spec (.of K)) hK}
    (hX : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (Stack.structureMorphism B (Spec (.of K)) hK X))
    {U : BigFppfOver B (Spec (.of K)) hK}
    (a : Stack.schemeStack B (Spec (.of K)) hK U ⟶ X)
    (ha : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK a) :
    Smooth (B.inclusion.map U.hom) := by
  apply (Stack.isSmooth_structureMorphism_schemeStack_iff B (Spec (.of K)) hK U).1
  simpa only [Stack.comp_structureMorphism] using
    Stack.AlgebraicStacks.isSmooth_comp B (Spec (.of K)) hK a _ ha hX

/-- Every native point is covered by one of finitely many actual integral
open components of the same affine atlas. The component maps are actual
smooth morphisms to the original stack. -/
theorem finite_integral_component_cover
    {X : Stack.AlgebraicStacks.{u, w} B (Spec (.of K)) hK}
    {U : BigFppfOver B (Spec (.of K)) hK}
    (a : Stack.schemeStack B (Spec (.of K)) hK U ⟶ X)
    (hsurj : Stack.IsSurjective B (Spec (.of K)) hK a)
    (ha : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK a)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U)]
    [Smooth (B.inclusion.map U.hom)] :
    ∃ t : Finset ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U),
      (∀ y ∈ t,
        IsIntegral (SmoothIntegralComponentCover.componentOpen (B.inclusion.map U.hom) y).toScheme ∧
        Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
          (openAtlasMap B (Spec (.of K)) hK a
            (SmoothIntegralComponentCover.componentOpen (B.inclusion.map U.hom) y))) ∧
      ∀ z : Stack.AlgebraicStacks.points B (Spec (.of K)) hK X,
        ∃ y ∈ t, z ∈ Set.range
          (schemePointMap B (Spec (.of K)) hK
            (openAtlasMap B (Spec (.of K)) hK a
              (SmoothIntegralComponentCover.componentOpen (B.inclusion.map U.hom) y))) := by
  let _ : IsAffine (B.inclusion.obj U.left) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U))
  let _ : CompactSpace (B.inclusion.obj U.left) := inferInstance
  obtain ⟨t, ht⟩ :=
    SmoothIntegralComponentCover.exists_finite_component_cover (B.inclusion.map U.hom)
  refine ⟨t, fun y _ => ⟨SmoothIntegralComponentCover.component_integral _ y,
    openAtlasMap_smooth B (Spec (.of K)) hK a ha _⟩, fun z => ?_⟩
  obtain ⟨q, hq⟩ := hsurj z
  let x := Stack.pointsHomeomorphScheme B (Spec (.of K)) hK U q
  obtain ⟨y, hyt, hxy⟩ := ht x
  refine ⟨y, hyt, ⟨⟨x, hxy⟩, ?_⟩⟩
  rw [schemePointMap_openAtlasMap]
  simpa only [schemePointMap, Function.comp_apply, Scheme.Opens.ι_apply, x,
    Homeomorph.symm_apply_apply] using hq

/-- Genuine structural smoothness and quasi-compactness produce the
affine atlas needed for the finite integral component cover. -/
theorem exists_affine_smooth_atlas
    (X : Stack.AlgebraicStacks.{u, w} B (Spec (.of K)) hK)
    (hX : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (Stack.structureMorphism B (Spec (.of K)) hK X))
    (hqc : Stack.IsQuasiCompactStack B (Spec (.of K)) hK X.val X.property) :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK)
      (a : Stack.schemeStack B (Spec (.of K)) hK U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hK).obj U) ∧
      Stack.IsSurjective B (Spec (.of K)) hK a ∧
      Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK a ∧
      Smooth (B.inclusion.map U.hom) := by
  obtain ⟨U, hU, a, hsurj, ha⟩ :=
    Stack.exists_affineAtlas_of_isQuasiCompactStack B (Spec (.of K)) hK X hqc
  exact ⟨U, a, hU, hsurj, ha, atlas_structural_smooth B K hK hX a ha⟩

end M9Native.SmoothStackIntegralAtlas

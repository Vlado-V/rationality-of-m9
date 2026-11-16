module

public import M9StacksIntegration.Private.PredeformationChangeBaseEquivalence
public import M9StacksIntegration.Private.FormalHullEquivalence

/-!
# The actual native field-base comparison of marked deformation categories

The original projection of the original two-fibre product gives the functor.
Its original compatible-arrow and object lifting properties prove that it is
an equivalence over the Artin category. The inverse therefore transports an
actual hull, with its unchanged complete local base, to the actual base change.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber

universe u w

namespace M9Native.AlgebraicStackBaseChangeEquivalence

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS') (𝒳 : Stack.AlgebraicStacks.{u,w} B S' hS')
  {k : Type u} [Field k] (iS : Spec (.of k) ⟶ S)
  (x₀ : (Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.obj)
  (hx₀ : (((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p) ⋙
    Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ iS))

include hx₀ in
/-- The original projected point has the actual composed base map. -/
theorem image_lies_over :
    (𝒳.val.val.p ⋙ Over.post B.inclusion).obj ((Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj x₀) = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫
      (iS ≫ B.inclusion.map g)) := by
  calc
    (𝒳.val.val.p ⋙ Over.post B.inclusion).obj ((Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj x₀) = (Over.map (B.inclusion.map g)).obj (((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion).obj x₀) :=
      Functor.congr_obj (Stack.algebraicStackBaseChangeProjection_comp
        B S S' hS hS' g 𝒳) x₀
    _ = _ := by
      rw [hx₀]
      change Over.mk ((Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ iS) ≫
        B.inclusion.map g) = _
      rw [Category.assoc]

/-- The original native deformation functor, with no supplied comparison. -/
abbrev comparison :=
  predeformationFunctorOfCompEqCompMap iS (B.inclusion.map g) ((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) (𝒳.val.val.p ⋙ Over.post B.inclusion) (Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳)
    (Stack.algebraicStackBaseChangeProjection_comp B S S' hS hS' g 𝒳)
    x₀ hx₀ (image_lies_over B S S' hS hS' g 𝒳 iS x₀ hx₀)

/-- The actual source and target lifting theorems prove equivalence. -/
theorem comparison_isEquivalence :
    letI := (predeformationCategory iS ((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ B.inclusion.map g) (𝒳.val.val.p ⋙ Over.post B.inclusion) ((Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj x₀)
      (image_lies_over B S S' hS hS' g 𝒳 iS x₀ hx₀)).category
    (comparison B S S' hS hS' g 𝒳 iS x₀ hx₀).toFunctor.IsEquivalence := by
  letI := (predeformationCategory iS ((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
  letI := (predeformationCategory (iS ≫ B.inclusion.map g) (𝒳.val.val.p ⋙ Over.post B.inclusion) ((Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj x₀)
    (image_lies_over B S S' hS hS' g 𝒳 iS x₀ hx₀)).category
  exact PredeformationChangeBaseEquivalence.isEquivalence iS (B.inclusion.map g) ((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) (𝒳.val.val.p ⋙ Over.post B.inclusion) (Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳)
    (Stack.algebraicStackBaseChangeProjection_comp B S S' hS hS' g 𝒳)
    x₀ hx₀ (image_lies_over B S S' hS hS' g 𝒳 iS x₀ hx₀)
    (Stack.liftsCompEqCompMap_algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳)
    (Stack.exists_algebraicStackBaseChangeProjection_obj_eq B S S' hS hS' g 𝒳)

/-- The genuine inverse is bundled over the unchanged Artin base. -/
def equivalence :
    letI := (predeformationCategory iS ((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
    letI := (predeformationCategory (iS ≫ B.inclusion.map g) (𝒳.val.val.p ⋙ Over.post B.inclusion) ((Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj x₀)
      (image_lies_over B S S' hS hS' g 𝒳 iS x₀ hx₀)).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformationCategory iS ((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection
      (predeformationCategory (iS ≫ B.inclusion.map g) (𝒳.val.val.p ⋙ Over.post B.inclusion) ((Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj x₀)
        (image_lies_over B S S' hS hS' g 𝒳 iS x₀ hx₀)).projection := by
  letI := (predeformationCategory iS ((Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
  letI := (predeformationCategory (iS ≫ B.inclusion.map g) (𝒳.val.val.p ⋙ Over.post B.inclusion) ((Stack.algebraicStackBaseChangeProjection B S S' hS hS' g 𝒳).obj x₀)
    (image_lies_over B S S' hS hS' g 𝒳 iS x₀ hx₀)).category
  let Ψ := comparison B S S' hS hS' g 𝒳 iS x₀ hx₀
  letI : Ψ.toFunctor.IsEquivalence :=
    comparison_isEquivalence B S S' hS hS' g 𝒳 iS x₀ hx₀
  exact equivalenceOverOfCofibered
    (predeformationCategory_isPredeformationCategory B hS iS
      (Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.val.p
      x₀ hx₀ (Stack.algebraicStackBaseChange B S S' hS hS' g 𝒳).val.property).cofibered
    Ψ.toFunctor Ψ.w

end M9Native.AlgebraicStackBaseChangeEquivalence

module

public import M9StacksIntegration.AlgebraicSpaceClassifierObjectEquality
public import M9StacksIntegration.NativeUniversalHomeomorphismGeometricLift

/-! Actual native classifiers with equal algebraic-space maps have a
same-field arrow over the identity under a genuine universal homeomorphism.
Image-object and base equalities are derived, not supplied as hypotheses. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.ASClassifierGeometricLift

universe u w
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {M : AlgebraicSpaces B S hS}

/-- The literal underlying native functor, with its original basedness
proof, read through the actual structure functor of 𝒴. -/
def coarseFunctor
    (f : 𝒴 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property) :
    BasedCategory.ofFunctor 𝒴.val.val.p ⥤ᵇ
      AlgebraicSpaceValuedClassifierReflection.target B S hS M where
  toFunctor := f.hom.hom.toFunctor
  w := f.hom.hom.w

/-- No source-model equivalence is assumed: the underlying classifier
functor and its basedness proof are retained literally. -/
def classifier {V : BigFppfOver B S hS}
    (A : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ 𝒴.val.val) :
    BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ BasedCategory.ofFunctor 𝒴.val.val.p where
  toFunctor := A.toFunctor
  w := A.w

/-- The actual AS morphism induced by the actual stack morphism f and
actual native classifier A. -/
def nativeMap
    (f : 𝒴 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    {V : BigFppfOver B S hS} (A : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ 𝒴.val.val) :
    schemeSpace V ⟶ M :=
  AlgebraicSpaceValuedClassifierReflection.nativeMap B S hS (coarseFunctor B S hS f)
    (classifier B S hS A)

/-- The SAME native base at the unit follows from actual basedness. -/
theorem unit_base_eq {V : BigFppfOver B S hS}
    (A : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ 𝒴.val.val) :
    𝒴.val.val.p.obj (A.toFunctor.obj (Functor.FiberedMor.unit V)) = V :=
  Functor.congr_obj A.w (Functor.FiberedMor.unit V)

/-- Equal actual AS maps derive equality of actual f-image objects. -/
theorem unit_image_eq_of_nativeMap_eq
    (f : 𝒴 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    {V : BigFppfOver B S hS}
    {A₁ A₂ : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ 𝒴.val.val}
    (h : nativeMap B S hS f A₁ = nativeMap B S hS f A₂) :
    f.hom.hom.obj (A₁.toFunctor.obj (Functor.FiberedMor.unit V)) =
      f.hom.hom.obj (A₂.toFunctor.obj (Functor.FiberedMor.unit V)) :=
  AlgebraicSpaceClassifierObjectEquality.unit_eq_of_nativeMap_eq B S hS
    (coarseFunctor B S hS f) h

/-- Under the genuine UH hypothesis, equal actual AS maps give an actual
arrow over id_V between the ORIGINAL native classifier unit objects.
The same ACL field is a genuine site object; no outside-site claim occurs. -/
theorem exists_isHomLift_id_of_nativeMap_eq
    (f : 𝒴 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : Stack.UniversalHomeomorphism B S hS f)
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (A₁ A₂ : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ 𝒴.val.val)
    (h : nativeMap B S hS f A₁ = nativeMap B S hS f A₂) :
    ∃ α : A₁.toFunctor.obj (Functor.FiberedMor.unit V) ⟶
        A₂.toFunctor.obj (Functor.FiberedMor.unit V),
      𝒴.val.val.p.IsHomLift (𝟙 V) α :=
  NativeUniversalHomeomorphismGeometricLift.exists_isHomLift_id f hf k V hV
    (A₁.toFunctor.obj (Functor.FiberedMor.unit V))
    (A₂.toFunctor.obj (Functor.FiberedMor.unit V))
    (unit_base_eq B S hS A₁) (unit_base_eq B S hS A₂)
    (unit_image_eq_of_nativeMap_eq B S hS f h)

end M9Native.ASClassifierGeometricLift

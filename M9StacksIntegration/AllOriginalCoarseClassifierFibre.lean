module

public import M9StacksIntegration.SimultaneousNativeGeometricModel
public import M9StacksIntegration.ASClassifierGeometricLift

/-! Actual coarse fibres on every original algebraically closed test field.
Equal original coarse values have a simultaneous native geometric model.
The genuine universal homeomorphism then gives a source arrow over the
identity of that SAME native field. Both original parameter maps and the
original coefficient map are retained for subsequent physical pullback.
There is no bounded-site membership hypothesis on the original field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.AllOriginalCoarseClassifierFibre
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalPullbacks

universe u w
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))
  {𝒴 : Stack.AlgebraicStacks.{u, w} B (Spec (.of K)) hK}
  {M : AlgebraicSpaces B (Spec (.of K)) hK}

/-- Native precomposition retains the literal actual coarse map. -/
theorem nativeMap_precompose
    (f : 𝒴 ⟶ Stack.algebraicSpaceStack.{u, w} B (Spec (.of K)) hK M.obj M.property)
    {U T : BigFppfOver B (Spec (.of K)) hK}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ 𝒴.val.val) (a : T ⟶ U) :
    ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f
        (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) A) =
      schemeSpaceMap a ≫ ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f A := by
  change AlgebraicSpaceValuedClassifierReflection.nativeMap B (Spec (.of K)) hK
      (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK f)
      (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a)
        (ASClassifierGeometricLift.classifier B (Spec (.of K)) hK A)) = _
  exact AlgebraicSpaceValuedClassifierReflection.nativeMap_precompose B (Spec (.of K)) hK
    (ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK f)
    (ASClassifierGeometricLift.classifier B (Spec (.of K)) hK A) a

/-- Equality of actual ORIGINAL coarse values yields an actual source arrow
on a simultaneous bounded model, over the identity of its ACL field.
The actual original points are recovered along one and the same map w. -/
theorem exists_simultaneous_source_arrow
    (f : 𝒴 ⟶ Stack.algebraicSpaceStack.{u, w} B (Spec (.of K)) hK M.obj M.property)
    (hf : Stack.UniversalHomeomorphism B (Spec (.of K)) hK f)
    (U V : BigFppfOver B (Spec (.of K)) hK)
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ 𝒴.val.val)
    (D : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ 𝒴.val.val)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj U)
    (y : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj V)
    (hxy : (originalChart K B hK M U
        (ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f A).hom).app
          (op (M9StandaloneDraft.FieldPoint K L)) x =
      (originalChart K B hK M V
        (ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f D).hom).app
          (op (M9StandaloneDraft.FieldPoint K L)) y) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (hΩ : B.Contains (Spec (.of Ω))) (sΩ : Spec (.of Ω) ⟶ Spec (.of K))
      (a : siteObject B (Spec (.of K)) hK hΩ sΩ ⟶ U)
      (b : siteObject B (Spec (.of K)) hK hΩ sΩ ⟶ V)
      (v : M9StandaloneDraft.FieldPoint K L ⟶
        (boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hΩ sΩ))
      (α : (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) A).toFunctor.obj
          (Functor.FiberedMor.unit (siteObject B (Spec (.of K)) hK hΩ sΩ)) ⟶
        (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap b) D).toFunctor.obj
          (Functor.FiberedMor.unit (siteObject B (Spec (.of K)) hK hΩ sΩ))),
      𝒴.val.val.p.IsHomLift (𝟙 (siteObject B (Spec (.of K)) hK hΩ sΩ)) α ∧
      v ≫ (boundedInclusion B K hK).map a = x ∧
      v ≫ (boundedInclusion B K hK).map b = y := by
  obtain ⟨Ω, hΩField, hΩClosed, hΩ, sΩ, a, b, v, hab, hx, hy⟩ :=
    SimultaneousNativeGeometricModel.exists_simultaneous_model K B hK M U V
      (ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f A).hom
      (ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f D).hom L x y hxy
  letI : Field Ω := hΩField
  letI : IsAlgClosed Ω := hΩClosed
  let Q := siteObject B (Spec (.of K)) hK hΩ sΩ
  let A₁ := BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) A
  let A₂ := BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap b) D
  have hm : ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f A₁ =
      ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK f A₂ := by
    dsimp only [A₁, A₂]
    rw [nativeMap_precompose K B hK f A a, nativeMap_precompose K B hK f D b]
    exact ObjectProperty.hom_ext _ hab
  obtain ⟨α, hα⟩ := ASClassifierGeometricLift.exists_isHomLift_id_of_nativeMap_eq
    B (Spec (.of K)) hK f hf Ω Q (Iso.refl _) A₁ A₂ hm
  exact ⟨Ω, hΩField, hΩClosed, hΩ, sΩ, a, b, v, α, hα, hx, hy⟩

end M9Native.AllOriginalCoarseClassifierFibre

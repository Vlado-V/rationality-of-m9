module

public import M9StacksIntegration.BoundedOriginalFamilyCoarseRecovery
public import M9StacksIntegration.NativeUniversalHomeomorphismGeometricLift
public import M9StacksIntegration.AllTestNativeFamilyFull

/-! Geometric injectivity of the ACTUAL chosen coarse value on every
original family over a native bounded geometric base. Total spaces may be
nonschematic. Actual source objects, their image equality, the identity-base
source arrow and its original recovery are all derived. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories

namespace M9Native.BoundedOriginalFamilyCoarseInjectivity
open BoundedOriginalFamilyCoarseValue BoundedOriginalFamilyCoarseRecovery
  M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeCurveFamily
  M9StacksIntegration.AllTestNativeFamilyFull

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)

section ImageEquality
variable
  {Q : BigFppfOver B (Spec (.of K)) hK}
  (F G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj Q) g)

/-- Equal actual chosen values name the same actual coarse image object. -/
theorem coarseImage_eq_of_nativeValue_eq
    (hFG : nativeValue B hZ K hK g hg F = nativeValue B hZ K hK g hg G) :
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom.obj
        (sourceObject B hZ K hK g hg F) =
      (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom.obj
        (sourceObject B hZ K hK g hg G) := by
  let κ := ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
  exact obj_eq_of_elementOf_eq
    (Functor.congr_obj κ.w (sourceObject B hZ K hK g hg F))
    (Functor.congr_obj κ.w (sourceObject B hZ K hK g hg G)) hFG

end ImageEquality

variable (k : Type u) [Field k] [IsAlgClosed k]
  (Q : BigFppfOver B (Spec (.of K)) hK)
  (hQ : (BigFppfOver.toScheme B (Spec (.of K)) hK).obj Q ≅ Spec (.of k))
  (F G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj Q) g)

include k hQ

/-- The genuine UH of the exact chosen coarse map gives a source arrow
over the identity of the SAME native geometric base. -/
theorem exists_source_arrow_of_nativeValue_eq
    (hFG : nativeValue B hZ K hK g hg F = nativeValue B hZ K hK g hg G) :
    ∃ α : sourceObject B hZ K hK g hg F ⟶ sourceObject B hZ K hK g hg G,
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.IsHomLift
        (𝟙 Q) α :=
  NativeUniversalHomeomorphismGeometricLift.exists_isHomLift_id
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap_universalHomeomorphism B hZ K hK g hg)
    k Q hQ (sourceObject B hZ K hK g hg F) (sourceObject B hZ K hK g hg G)
    (sourceObject_base B hZ K hK g hg F) (sourceObject_base B hZ K hK g hg G)
    (coarseImage_eq_of_nativeValue_eq B hZ K hK g hg F G hFG)

/-- Actual hom-shrink recovery conjugates the actual source arrow to a
native arrow of the SAME original families with the identity base map. -/
theorem exists_native_identity_arrow_of_nativeValue_eq
    (hFG : nativeValue B hZ K hK g hg F = nativeValue B hZ K hK g hg G) :
    ∃ δ : nativeCurveFamily B hZ K hK F ⟶ nativeCurveFamily B hZ K hK G,
      δ.baseMap = 𝟙 (nativeBase B hZ K hK Q) := by
  obtain ⟨α, hα⟩ := exists_source_arrow_of_nativeValue_eq B hZ K hK g hg k Q hQ F G hFG
  let p := curvesProjectionOver B hZ
  let eF := sourceObject_originalIso B hZ K hK g hg F
  let eG := sourceObject_originalIso B hZ K hK g hg G
  let β := (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).map α
  have hβ : p.IsHomLift (𝟙 (nativeBase B hZ K hK Q)) β :=
    NativeSmoothGenusCoarseClassifier.original_isHomLift_id B hZ K hK g hg Q α hα
  have hrecovery (H : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj Q) g) :
      p.IsHomLift (𝟙 (nativeBase B hZ K hK Q))
        (sourceObject_originalIso B hZ K hK g hg H).hom := by
    apply IsHomLift.of_fac' (curvesProjectionOver B hZ)
      (𝟙 (nativeBase B hZ K hK Q)) (sourceObject_originalIso B hZ K hK g hg H).hom
      (sourceObject_original_base B hZ K hK g hg H) rfl
    simpa only [p, curvesProjectionOver, eqToHom_refl, Category.comp_id, Category.id_comp] using
      sourceObject_originalIso_baseMap B hZ K hK g hg H
  letI := hrecovery F
  letI := hrecovery G
  letI := hβ
  have hFinv : p.IsHomLift (𝟙 (nativeBase B hZ K hK Q)) eF.inv := inferInstance
  letI := hFinv
  let δ := eF.inv ≫ β ≫ eG.hom
  have hδ : p.IsHomLift (𝟙 (nativeBase B hZ K hK Q)) δ := by
    have : p.IsHomLift (𝟙 (nativeBase B hZ K hK Q)) (β ≫ eG.hom) :=
      IsHomLift.comp_lift_id_left p (𝟙 (nativeBase B hZ K hK Q)) _ _
    exact IsHomLift.comp_lift_id_left p (𝟙 (nativeBase B hZ K hK Q)) _ _
  letI := hδ
  refine ⟨δ, ?_⟩
  simpa only [p, curvesProjectionOver, nativeCurveFamily_base,
    eqToHom_refl, Category.comp_id, Category.id_comp] using
    (IsHomLift.fac' p (𝟙 (nativeBase B hZ K hK Q)) δ)

/-- Equal values of the ACTUAL chosen coarse map identify ORIGINAL family
isomorphism classes over this geometric base, including nonschematic totals. -/
theorem familyIsomorphic_of_nativeValue_eq
    (hFG : nativeValue B hZ K hK g hg F = nativeValue B hZ K hK g hg G) :
    M9StandaloneDraft.FamilyIsomorphic K F G :=
  (familyIsomorphic_iff_native_identity_arrow B hZ K hK F G).2
    (exists_native_identity_arrow_of_nativeValue_eq B hZ K hK g hg k Q hQ F G hFG)

end M9Native.BoundedOriginalFamilyCoarseInjectivity

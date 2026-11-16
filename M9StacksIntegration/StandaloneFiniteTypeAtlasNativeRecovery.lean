module

public import M9StacksIntegration.AllTestBoundedOriginalRecovery
public import M9StacksIntegration.AllTestNativeOriginalFunctor
public import M9StacksIntegration.AllTestNativeOriginalVarietyAtlas
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-! An original space with an actual finite-type atlas is recovered on
every fixed native site containing its coefficient field. The atlas size
bound is derived; no native presentation or site-comparison is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.StandaloneFiniteTypeAtlasNativeRecovery

open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestBoundedRestriction
  M9StacksIntegration.AllTestBoundedSpaceTargets
  M9StacksIntegration.AllTestBoundedOriginalRecovery
  M9StacksIntegration.AllTestNativeOriginalSpace
  M9StacksIntegration.AllTestNativeOriginalFunctor

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
    (hK : B.Contains (Spec (.of K)))

/-- A genuine finite-type atlas lies in every native site containing the
field, so the actual bounded restriction recovers the same original Space. -/
theorem exists_native_recovery (W : M9StandaloneDraft.Space K)
    (U : M9StandaloneDraft.Schemes K) (a : yoneda.obj U ⟶ W.obj)
    (hae : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (has : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] :
    ∃ F : AlgebraicSpaces B (Spec (.of K)) hK,
      Nonempty ((originalPresheafFunctor K B hK).obj F ≅ W.obj) := by
  have hU : B.Contains U.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact U.hom hK
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  let Un := siteObject B (Spec (.of K)) hK hU Uhom
  let hW := isAlgebraicSpace_restrict_of_bounded_atlas K B hK W
    ((boundedInclusion B K hK).obj Un) hU a hae has
  let F : AlgebraicSpaces B (Spec (.of K)) hK := ⟨restrict K B hK W.obj, hW⟩
  exact ⟨F, ⟨originalOfRestrictionIso_of_bounded_atlas K B hK W Un a hae has⟩⟩

/-- The original image of any genuine native LFT/QC space is recovered
on every other fixed site containing the same coefficient field. No
reducedness, separatedness or coarseness premise is required. -/
theorem exists_native_recovery_of_native_finiteType
    (Bsrc : BigFppfSite.{u}) (hKsrc : Bsrc.Contains (Spec (.of K)))
    (X : AlgebraicSpaces Bsrc (Spec (.of K)) hKsrc)
    (hf : Space.IsLocallyOfFiniteType Bsrc (Spec (.of K)) hKsrc
      ((Space.isTerminal_yoneda_obj_base Bsrc (Spec (.of K)) hKsrc).from X.obj))
    (hc : Space.IsQuasiCompactSpace Bsrc (Spec (.of K)) hKsrc X.obj) :
    ∃ F : AlgebraicSpaces B (Spec (.of K)) hK,
      Nonempty ((originalPresheafFunctor K B hK).obj F ≅
        (originalPresheafFunctor K Bsrc hKsrc).obj X) := by
  obtain ⟨U, a, hae, has, hfU, hcU⟩ :=
    M9StacksIntegration.AllTestNativeOriginalVarietyAtlas.exists_original_finiteType_atlas
      K Bsrc hKsrc X.obj X.property hf hc
  let : LocallyOfFiniteType U.hom := hfU
  let : QuasiCompact U.hom := hcU
  exact exists_native_recovery K B hK
    (originalSpaceOfNative K Bsrc hKsrc X.obj X.property) U a hae has

end M9Native.StandaloneFiniteTypeAtlasNativeRecovery

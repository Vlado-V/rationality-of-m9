module

public import M9StacksIntegration.AllTestBoundedOriginalRecovery
public import M9StacksIntegration.AllTestNativeOriginalFunctor

/-!
# EVERY original algebraic space has an actual native presentation

Each literal original algebraic space, together with any small collection
of prescribed ORIGINAL schemes, admits an actual native site and an actual
native algebraic space whose full-original extension is isomorphic to the
SAME original presheaf. This chooses a site from the actual original atlas
and prescribed schemes, and uses proved actual bounded-atlas recovery.

No fixed cutoff is imposed on the standalone test category, and no native
presentation, classifier or comparison equivalence is supplied as a premise.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalEssentialImage
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedSpaceTargets
  AllTestBoundedOriginalRecovery AllTestNativeOriginalFunctor
universe u
variable (K : Type u) [Field K]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- EVERY original algebraic-space target is the actual original image of
an actual native space, on a site also containing any prescribed small
collection of original schemes. The actual atlas constructs the site. -/
theorem exists_site_original_recovery (W : M9StandaloneDraft.Space K)
    (S : Set Scheme.{u}) [Small.{u} S] :
    ∃ (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))),
      (∀ T ∈ S, B.Contains T) ∧
      ∃ F : AlgebraicSpaces B (Spec (.of K)) hK,
        Nonempty ((originalPresheafFunctor K B hK).obj F ≅ W.obj) := by
  obtain ⟨U, a, he, hs⟩ := W.atlas
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing (S ∪ {Spec (.of K), U.left})
  have hK : B.Contains (Spec (.of K)) := hB _ (by simp)
  have hU : B.Contains U.left := hB _ (by simp)
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  let Un := siteObject B (Spec (.of K)) hK hU Uhom
  let hW := isAlgebraicSpace_restrict_of_bounded_atlas K B hK W
    ((boundedInclusion B K hK).obj Un) hU a he hs
  let F : AlgebraicSpaces B (Spec (.of K)) hK := ⟨restrict K B hK W.obj, hW⟩
  refine ⟨B, hK, fun T hT => hB T (Or.inl hT), F, ?_⟩
  exact ⟨originalOfRestrictionIso_of_bounded_atlas K B hK W Un a he hs⟩

end M9StacksIntegration.AllTestNativeOriginalEssentialImage

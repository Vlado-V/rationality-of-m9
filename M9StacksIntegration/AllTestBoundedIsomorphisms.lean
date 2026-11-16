module

public import M9StacksIntegration.AllTestBoundedFull

/-!
# Actual map equivalence and isomorphism reflection on family totals

Fullness and faithfulness of the bounded K-site comparison were proved by
actual original atlas descent. This file packages that conclusion as an
actual equivalence of morphism types and reflects isomorphisms on the
unchanged original family totals.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedIsomorphisms
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedAlgebraicSpace
  AllTestBoundedFull AllTestBoundedFaithful
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The actual bounded restriction is a bijection on maps from an original
family total to ANY original sheaf. -/
theorem restrictMap_bijective_from_family
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (H : M9StandaloneDraft.Presheaves K)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) H) :
    Function.Bijective (fun d : F.total.obj ⟶ H => restrictMap K B hK d) := by
  refine ⟨fun _ _ h => restrictMap_injective_from_family K B hK F H hH h, ?_⟩
  intro n
  obtain ⟨d, hd, _⟩ := existsUnique_lift_restrictMap_from_family K B hK F H hH n
  exact ⟨d, hd⟩

/-- Equivalence with the real restriction map as its forward function. -/
def homEquiv_from_family
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (H : M9StandaloneDraft.Presheaves K)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) H) :
    (F.total.obj ⟶ H) ≃ (restrict K B hK F.total.obj ⟶ restrict K B hK H) :=
  Equiv.ofBijective _ (restrictMap_bijective_from_family K B hK F H hH)

/-- An isomorphism of the actual bounded restrictions implies an isomorphism
of the entire original family totals. The original bases may differ. -/
theorem isIso_of_isIso_restrictMap
    {T U : BigFppfOver B (Spec (.of K)) hK} {g h : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) h)
    (r : F.total.obj ⟶ G.total.obj) [IsIso (restrictMap K B hK r)] : IsIso r := by
  let L := restrictionFunctor K B hK
  obtain ⟨d, hd, _⟩ := existsUnique_lift_restrictMap_from_family K B hK G F.total.obj
    F.total.isSheaf (inv (restrictMap K B hK r))
  have hrd : r ≫ d = 𝟙 _ := by
    apply restrictMap_injective_from_family K B hK F F.total.obj F.total.isSheaf
    change L.map (r ≫ d) = L.map (𝟙 _)
    rw [L.map_comp, L.map_id]
    change restrictMap K B hK r ≫ restrictMap K B hK d = 𝟙 _
    rw [hd, IsIso.hom_inv_id]
  have hdr : d ≫ r = 𝟙 _ := by
    apply restrictMap_injective_from_family K B hK G G.total.obj G.total.isSheaf
    change L.map (d ≫ r) = L.map (𝟙 _)
    rw [L.map_comp, L.map_id]
    change restrictMap K B hK d ≫ restrictMap K B hK r = 𝟙 _
    rw [hd, IsIso.inv_hom_id]
  exact ⟨⟨d, hrd, hdr⟩⟩

end M9StacksIntegration.AllTestBoundedIsomorphisms

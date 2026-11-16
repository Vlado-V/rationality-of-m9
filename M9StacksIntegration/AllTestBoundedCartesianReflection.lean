module

public import M9StacksIntegration.AllTestBoundedIsomorphisms
public import M9StacksIntegration.AllTestFamilyPullback

/-!
# Actual cartesian reflection from a bounded site

Every original family base change is already constructed on the full original
category. Comparing it with a proposed square gives a map of original family
totals. The bounded comparison map is an isomorphism by the two actual
pullback universal properties. Proved full faithfulness then reflects that
isomorphism, yielding the full original cartesian square.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedCartesianReflection
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedAlgebraicSpace AllTestBoundedFaithful AllTestBoundedIsomorphisms
  AllTestSchemeFamilies AllTestFamilyPullback
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- A cartesian square of bounded restrictions of actual original families
is cartesian on EVERY original test scheme. -/
theorem isPullback_of_restrict_isPullback
    {T U : BigFppfOver B (Spec (.of K)) hK} {g h : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) h)
    (a : U ⟶ T) (r : G.total.obj ⟶ F.total.obj)
    (hn : IsPullback (restrictMap K B hK r) (restrictMap K B hK G.projection)
      (restrictMap K B hK F.projection)
      (restrictMap K B hK (yoneda.map ((boundedInclusion B K hK).map a)))) :
    IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map a)) := by
  let L := restrictionFunctor K B hK
  let a₀ := (boundedInclusion B K hK).map a
  let : HasPullback F.projection (yoneda.map a₀) :=
    originalPresheafPullback K F.projection (yoneda.map a₀)
  have hw : r ≫ F.projection = G.projection ≫ yoneda.map a₀ := by
    apply restrictMap_injective_from_family K B hK G
      (yoneda.obj ((boundedInclusion B K hK).obj T))
      (standaloneSchemeSpace K ((boundedInclusion B K hK).obj T)).isSheaf
    change L.map (r ≫ F.projection) = L.map (G.projection ≫ yoneda.map a₀)
    rw [L.map_comp, L.map_comp]
    exact hn.w
  let P := pullbackFamily K F a₀
  let c : G.total.obj ⟶ P.total.obj := pullback.lift r G.projection hw
  have hcf : c ≫ pullback.fst F.projection (yoneda.map a₀) = r :=
    pullback.lift_fst _ _ _
  have hcs : c ≫ P.projection = G.projection := pullback.lift_snd _ _ _
  have hp := pullbackFamily_isPullback K F a₀
  have hpn := restrict_isPullback K B hK hp
  let e := hn.isoIsPullback _ _ hpn
  have hce : restrictMap K B hK c = e.hom := by
    apply hpn.hom_ext
    · calc
        restrictMap K B hK c ≫
            restrictMap K B hK (pullback.fst F.projection (yoneda.map a₀)) =
          restrictMap K B hK (c ≫ pullback.fst F.projection (yoneda.map a₀)) :=
            (L.map_comp _ _).symm
        _ = restrictMap K B hK r := congrArg (fun m => restrictMap K B hK m) hcf
        _ = e.hom ≫ restrictMap K B hK (pullback.fst F.projection (yoneda.map a₀)) :=
          (hn.isoIsPullback_hom_fst _ _ hpn).symm
    · calc
        restrictMap K B hK c ≫ restrictMap K B hK P.projection =
          restrictMap K B hK (c ≫ P.projection) := (L.map_comp _ _).symm
        _ = restrictMap K B hK G.projection := congrArg (fun m => restrictMap K B hK m) hcs
        _ = e.hom ≫ restrictMap K B hK P.projection :=
          (hn.isoIsPullback_hom_snd _ _ hpn).symm
  let : IsIso (restrictMap K B hK c) := by
    rw [hce]
    exact Iso.isIso_hom e
  let : IsIso c := isIso_of_isIso_restrictMap K B hK G P c
  have hleft : IsPullback c G.projection P.projection (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hcs⟩
  have hfull := hleft.paste_horiz hp
  simpa only [hcf, Category.id_comp] using hfull

end M9StacksIntegration.AllTestBoundedCartesianReflection

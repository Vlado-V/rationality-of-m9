module

public import M9StacksIntegration.AllTestNativeChosenAtlas
public import M9StacksIntegration.StandaloneSchemeVariety
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic

/-!
# Reducedness and finite-type atlases on the full original site

Actual native reducedness gives reducedness of every original etale chart
by a genuine represented fibre product and flat descent. Native local
finite type and quasi-compactness give a finite-type original atlas with
the same original compact chart scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalVarietyAtlas
open AllTestBoundedCharts AllTestNativeOriginalSpace AllTestNativeChosenAtlas
universe u
variable (K : Type u) [Field K]

/-- A genuine reduced surjective etale atlas proves reducedness on EVERY
original etale chart, including charts outside any bounded site. -/
theorem etale_chart_reduced_of_atlas (M : M9StandaloneDraft.Space K)
    (U : M9StandaloneDraft.Schemes K) [IsReduced U.left]
    (a : yoneda.obj U ⟶ M.obj)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (V : M9StandaloneDraft.Schemes K) (v : yoneda.obj V ⟶ M.obj)
    (hv : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf v) : IsReduced V.left := by
  let R := he.rep.pullback v
  let s : R ⟶ V := he.rep.snd v
  let r : R ⟶ U := yoneda.preimage (he.rep.fst v)
  have hR : IsPullback (yoneda.map r) (yoneda.map s) a v := by
    rw [yoneda.map_preimage]
    exact he.rep.isPullback v
  have : Etale r.left := hv.property a (yoneda.map s) r hR.flip
  have : IsReduced R.left := AlgebraicGeometry.isReduced_of_etale r.left
  have : Etale s.left := he.property v (yoneda.map r) s hR
  have : Surjective s.left := hs.property v (yoneda.map r) s hR
  exact AlgebraicGeometry.isReduced_of_flat_of_surjective s.left

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

/-- Genuine native etale-local reducedness gives reducedness on every
actual etale chart of the SAME constructed original algebraic space. -/
theorem originalSpace_etale_chart_reduced
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (hr : Space.HasEtaleLocalProperty B (Spec (.of K)) hK F
      (fun X : Scheme.{u} => IsReduced X))
    (V : M9StandaloneDraft.Schemes K)
    (v : yoneda.obj V ⟶ (originalSpaceOfNative K B hK F hF).obj)
    (hv : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf v) : IsReduced V.left := by
  obtain ⟨U, a, hs, he, hU⟩ := hr
  have : IsReduced ((boundedInclusion B K hK).obj U).left := hU
  obtain ⟨he', hs'⟩ := originalChart_geometry K B hK F hF U a hs he
  exact etale_chart_reduced_of_atlas K (originalSpaceOfNative K B hK F hF)
    ((boundedInclusion B K hK).obj U) (originalChart K B hK F hF U a) he' hs' V v hv

/-- Native local finite type forces the SAME structural scheme morphism
of any genuine native etale chart to be locally of finite type. -/
theorem native_chart_locallyOfFiniteType
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hf : Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from F))
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ F)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf a) :
    LocallyOfFiniteType ((boundedInclusion B K hK).obj U).hom := by
  let T : BigFppfOver B (Spec (.of K)) hK := Over.mk (𝟙 (B.obj hK))
  let f : U ⟶ T := Over.homMk U.hom (by simp [T])
  have hid := Space.presheaf_etale_of_iso B (Spec (.of K)) hK (Iso.refl (yoneda.obj T))
  exact hf U T a (𝟙 _) f he hid
    ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).hom_ext _ _)

/-- Genuine native local finite type and quasi-compactness produce an
actual original surjective etale atlas of finite type over the original field. -/
theorem exists_original_finiteType_atlas
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (hf : Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from F))
    (hc : Space.IsQuasiCompactSpace B (Spec (.of K)) hK F) :
    ∃ (U : M9StandaloneDraft.Schemes K)
      (a : yoneda.obj U ⟶ (originalSpaceOfNative K B hK F hF).obj),
      (MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf a ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf a ∧
      LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom := by
  obtain ⟨U, a, hU, hs, he⟩ := hc
  have he' := (Space.isEtale_iff_presheaf_of_yoneda B (Spec (.of K)) hK a).mp he
  have : CompactSpace ((boundedInclusion B K hK).obj U).left := hU
  have : LocallyOfFiniteType ((boundedInclusion B K hK).obj U).hom :=
    native_chart_locallyOfFiniteType K B hK F hf U a he'
  obtain ⟨hae, has⟩ := originalChart_geometry K B hK F hF U a hs he'
  exact ⟨(boundedInclusion B K hK).obj U, originalChart K B hK F hF U a,
    hae, has, inferInstance, inferInstance⟩

end M9StacksIntegration.AllTestNativeOriginalVarietyAtlas

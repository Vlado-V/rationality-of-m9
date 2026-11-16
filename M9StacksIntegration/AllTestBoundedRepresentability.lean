module

public import M9StacksIntegration.AllTestBoundedCartesian
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism

/-!
# Actual representability on the bounded test site

A represented pullback on the original all-test site is still represented on
the bounded site whenever its scheme belongs there. For a monomorphism this
membership is proved by the native strong-prelimit size theorem, without
adding a finite-presentation or quasi-compactness assumption.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedRepresentability
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- A bounded representable section gives a map on the original all-test
category by the actual Yoneda correspondence. -/
def sectionMap {F : M9StandaloneDraft.Presheaves K}
    (V : BigFppfOver B (Spec (.of K)) hK)
    (g : yoneda.obj V ⟶ restrict K B hK F) :
    yoneda.obj ((boundedInclusion B K hK).obj V) ⟶ F :=
  yonedaEquiv.symm (g.app (Opposite.op V) (𝟙 V))

/-- This actual all-test section restricts to the section we started with. -/
theorem chartMap_sectionMap {F : M9StandaloneDraft.Presheaves K}
    (V : BigFppfOver B (Spec (.of K)) hK)
    (g : yoneda.obj V ⟶ restrict K B hK F) :
    chartMap K B hK V (sectionMap K B hK V g) = g := by
  apply yonedaEquiv.injective
  change F.map (((boundedInclusion B K hK).map (𝟙 V)).op)
      (g.app (Opposite.op V) (𝟙 V)) = g.app (Opposite.op V) (𝟙 V)
  exact ConcreteCategory.congr_hom
    ((restrict K B hK F).map_id (Opposite.op V)) (g.app (Opposite.op V) (𝟙 V))

/-- The represented cartesian square restricts with the actual bounded
representables at both left corners, for an arbitrary target presheaf. -/
theorem representable_isPullback {F G : M9StandaloneDraft.Presheaves K}
    (f : F ⟶ G) {Z V : BigFppfOver B (Spec (.of K)) hK} (s : Z ⟶ V)
    (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ F)
    (g : yoneda.obj ((boundedInclusion B K hK).obj V) ⟶ G)
    (h : IsPullback r (yoneda.map ((boundedInclusion B K hK).map s)) f g) :
    IsPullback (chartMap K B hK Z r) (yoneda.map s) (restrictMap K B hK f)
      (chartMap K B hK V g) := by
  apply (restrict_isPullback K B hK h).of_iso
    (restrictRepresentableIso B K hK Z) (Iso.refl _)
    (restrictRepresentableIso B K hK V) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, chartMap, Iso.hom_inv_id_assoc]
  · exact restrictRepresentableIso_naturality K B hK s
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, chartMap, Iso.hom_inv_id_assoc]

/-- Genuine restriction of relative representability. The auxiliary bound
is on the actual represented pullback schemes and is discharged below for
monomorphisms by a proved size bound. -/
theorem restrict_relativelyRepresentable_of_bounded_pullbacks
    {F G : M9StandaloneDraft.Presheaves K} (f : F ⟶ G)
    (hf : yoneda.relativelyRepresentable f)
    (hb : ∀ (V : BigFppfOver B (Spec (.of K)) hK)
      (g : yoneda.obj ((boundedInclusion B K hK).obj V) ⟶ G)
      (Z : M9StandaloneDraft.Schemes K)
      (s : Z ⟶ (boundedInclusion B K hK).obj V) (r : yoneda.obj Z ⟶ F),
      IsPullback r (yoneda.map s) f g → B.Contains Z.left) :
    yoneda.relativelyRepresentable (restrictMap K B hK f) := by
  intro V g
  let g₀ := sectionMap K B hK V g
  obtain ⟨Z, s, r, h⟩ := hf g₀
  have hZ := hb V g₀ Z s r h
  rcases Z with ⟨Z, ⟨⟨⟩⟩, Zhom⟩
  let Zn := siteObject B (Spec (.of K)) hK hZ Zhom
  let sn : Zn ⟶ V := boundedPreimage B K hK s
  refine ⟨Zn, sn, chartMap K B hK Zn r, ?_⟩
  have hn := representable_isPullback K B hK f sn r g₀ h
  rw [chartMap_sectionMap] at hn
  exact hn

/-- A representable original monomorphism remains representable on the
bounded site. Arbitrary monomorphisms, without a finite-presentation or
quasi-compactness hypothesis, suffice by the strong-prelimit cutoff bound. -/
theorem restrict_relativelyRepresentable_of_mono
    {F G : M9StandaloneDraft.Presheaves K} (f : F ⟶ G) [Mono f]
    (hf : yoneda.relativelyRepresentable f) :
    yoneda.relativelyRepresentable (restrictMap K B hK f) := by
  apply restrict_relativelyRepresentable_of_bounded_pullbacks K B hK f hf
  intro V g Z s r h
  let : Mono (yoneda.map s) := h.mono_snd_of_mono
  let : Mono s := yoneda.mono_of_mono_map inferInstance
  exact Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit s.left V.left.property

end M9StacksIntegration.AllTestBoundedRepresentability

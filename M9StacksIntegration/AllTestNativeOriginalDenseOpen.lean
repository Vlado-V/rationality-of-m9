module

public import M9StacksIntegration.AllTestNativeOriginalOpenSpace
public import M9StacksIntegration.AllTestNativeOriginalPropertyReflection
public import M9StacksIntegration.NativeDenseChartPullback
public import M9StacksIntegration.AllTestDenseOpenChartDescent

/-!
# Genuine native density transfers to the literal original dense-open condition

The actual bounded original atlas recovers an actual native etale chart.
Native point density yields ordinary density of its represented scheme
pullback; original etale-chart descent then retains density on EVERY
original represented etale pullback, including unbounded test schemes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.AllTestNativeOriginalDenseOpen
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalSpace
  AllTestNativeOriginalPullbacks AllTestNativeOriginalPropertyReflection
attribute [local instance] Space.pointTopology

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- A genuine native dense open immersion of arbitrary algebraic spaces
gives the literal original dense-open immersion, on every original test.
No original density, open immersion or chart-compatibility premise is supplied. -/
theorem denseOpen_of_native
    {X Y : AlgebraicSpaces B (Spec (.of K)) hK} (f : X ⟶ Y)
    (hf : Space.IsOpenImmersion B (Spec (.of K)) hK f.hom)
    (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK X.obj f.hom)) :
    M9StandaloneDraft.DenseOpen K ((originalPresheafFunctor K B hK).map f) := by
  have ho := AllTestNativeOriginalOpenSpace.openImmersion_of_native K B hK f hf
  obtain ⟨U, a, hae, has⟩ :=
    AllTestNativeOriginalAtlas.exists_bounded_original_atlas K B hK Y.obj Y.property
  let q := nativeChartOfOriginal K B hK Y U a
  have hqe : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf q.hom :=
    nativeChartOfOriginal_presheafProperty K B hK (@Etale.{u}) Y U a hae
  let V := hf.rep.pullback q.hom
  let b : yoneda.obj V ⟶ X.obj := hf.rep.fst q.hom
  let r : V ⟶ U := hf.rep.snd q.hom
  have hn : IsPullback b (yoneda.map r) f.hom q.hom := hf.rep.isPullback q.hom
  have hr : DenseRange ((BigFppfOver.toScheme B (Spec (.of K)) hK).map r) :=
    NativeDenseChartPullback.denseRange_toScheme_of_isPullback
      B (Spec (.of K)) hK f.hom b r q.hom hn hqe hd
  have hp := originalChart_isPullback K B hK f b r q.hom hn
  rw [originalChart_nativeChartOfOriginal K B hK Y U a] at hp
  exact AllTestDenseOpenChartDescent.denseOpen_of_chart K
    ((originalPresheafFunctor K B hK).map f) ho
    ((boundedInclusion B K hK).obj U) ((boundedInclusion B K hK).obj V)
    a hae has (originalChart K B hK X V b) ((boundedInclusion B K hK).map r) hp hr

end M9StacksIntegration.AllTestNativeOriginalDenseOpen

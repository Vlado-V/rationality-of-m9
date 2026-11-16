module

public import M9StacksIntegration.StandaloneDenseOpen

/-!
# Genuine density descent from one actual original etale atlas

The common represented pullback with any original etale chart has dense
image by the actual scheme etale base-change theorem. Its surjective map
to that test chart then proves density of the ORIGINAL represented map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.AllTestDenseOpenChartDescent

variable (K : Type u) [Field K]

/-- Density on an actual represented surjective-etale chart proves the
literal all-original-test dense-open condition. No geometric-point or
bounded-test replacement is made. -/
theorem denseOpen_of_chart
    {F G : M9StandaloneDraft.Presheaves K} (f : F ⟶ G)
    (hf : M9StandaloneDraft.OpenImmersion K f)
    (U V : M9StandaloneDraft.Schemes K) (a : yoneda.obj U ⟶ G)
    (hae : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (has : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (b : yoneda.obj V ⟶ F) (r : V ⟶ U)
    (h : IsPullback b (yoneda.map r) f a) (hr : DenseRange r.left) :
    M9StandaloneDraft.DenseOpen K f := by
  refine ⟨hf, ?_⟩
  intro T g hg P p c hp
  let H := hae.rep.pullback g
  let v : H ⟶ U := hae.rep.fst' g
  let q : H ⟶ T := hae.rep.snd g
  have hH : IsPullback (yoneda.map v) (yoneda.map q) a g := hae.rep.isPullback' g
  have hqs : Surjective q.left := has.property g (yoneda.map v) q hH
  have hve : Etale v.left := hg.property a (yoneda.map q) v hH.flip
  haveI : Etale v.left := hve
  let R := pullback r v
  let k : R ⟶ V := pullback.fst r v
  let s : R ⟶ H := pullback.snd r v
  have hbase : IsPullback k s r v := IsPullback.of_hasPullback r v
  have hOuter := (hbase.map yoneda).paste_horiz h
  let αN : yoneda.obj R ⟶ yoneda.obj P := hp.lift
    (yoneda.map k ≫ b) (yoneda.map s ≫ yoneda.map q)
    (by simpa only [Category.assoc, hH.w] using hOuter.w)
  let α : R ⟶ P := yoneda.preimage αN
  have hαN : yoneda.map α = αN := yoneda.map_preimage _
  have hα : α ≫ p = s ≫ q := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hαN, Functor.map_comp]
    exact hp.lift_snd _ _ _
  have hs : DenseRange s.left := M9Native.EtaleDensePullback.denseRange_of_isPullback
    r.left v.left k.left s.left
    (hbase.map (Over.forget (M9StandaloneDraft.Base K))) hr
  have hq : DenseRange q.left := hqs.surj.denseRange
  have hc : DenseRange ((s ≫ q).left) := hq.comp hs q.left.continuous
  rw [← hα] at hc
  exact DenseRange.of_comp (f := p.left) (g := α.left) hc

end M9StacksIntegration.AllTestDenseOpenChartDescent

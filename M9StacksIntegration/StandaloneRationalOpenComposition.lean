module

public import M9StacksIntegration.StandaloneDenseOpen

/-! Composition of genuine dense opens on the full original scheme site.
The intermediate open is represented; the final target may be an algebraic
space which is not a scheme. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9Native.StandaloneRationalOpenComposition

variable (K : Type u) [Field K]

local instance etalePropertyStable :
    (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).IsStableUnderBaseChange where
  of_isPullback h hg :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (h.map (Over.forget (M9StandaloneDraft.Base K))) hg

/-- A dense open in a represented dense open remains dense after every
actual etale chart of the final, possibly nonschematic, target. -/
theorem denseOpen_comp {U V : M9StandaloneDraft.Schemes K}
    {M : M9StandaloneDraft.Presheaves K}
    (i : yoneda.obj U ⟶ yoneda.obj V) (j : yoneda.obj V ⟶ M)
    (hi : M9StandaloneDraft.DenseOpen K i)
    (hj : M9StandaloneDraft.DenseOpen K j) :
    M9StandaloneDraft.DenseOpen K (i ≫ j) := by
  refine ⟨?_, ?_⟩
  · exact MorphismProperty.comp_mem
      ((MorphismProperty.inverseImage (@IsOpenImmersion.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf) i j hi.1 hj.1
  intro W v hv P a b hp
  let rep := hj.1.rep
  let Q := rep.pullback v
  let r : Q ⟶ V := yoneda.preimage (rep.fst v)
  have hOuter : IsPullback (yoneda.map r) (yoneda.map (rep.snd v)) j v := by
    simpa only [r, yoneda.map_preimage] using rep.isPullback v
  have hr : Etale r.left := hv.2 j (yoneda.map (rep.snd v)) r hOuter.flip
  letI := hr
  have hrPresheaf :
      (MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget (M9StandaloneDraft.Base K))).presheaf (yoneda.map r) :=
    MorphismProperty.relative_map (show Etale r.left by infer_instance)
  have hLift : (b ≫ i) ≫ j = yoneda.map a ≫ v := by
    simpa only [Category.assoc] using hp.w
  let k : P ⟶ Q := rep.lift (b ≫ i) a hLift
  have hk : k ≫ rep.snd v = a := rep.lift_snd _ _ _
  have hki : b ≫ i = yoneda.map k ≫ yoneda.map r := by
    simpa only [k, r, yoneda.map_preimage] using (rep.lift_fst (b ≫ i) a hLift).symm
  have hInner : IsPullback b (yoneda.map k) i (yoneda.map r) := by
    apply IsPullback.of_bot (t := hOuter) ?_ hki
    simpa only [← yoneda.map_comp, hk] using hp
  have hkd : DenseRange k.left := hi.2 Q (yoneda.map r) hrPresheaf P k b hInner
  have hqd : DenseRange (rep.snd v).left :=
    hj.2 W v hv Q (rep.snd v) (yoneda.map r) hOuter
  have ha : k.left ≫ (rep.snd v).left = a.left := congrArg Over.Hom.left hk
  rw [← ha]
  exact hqd.comp hkd (rep.snd v).left.continuous

/-- A rational common open of a represented dense open is a genuine
rational common open of the final target, over the original coefficient
field and with the same actual affine-space map. -/
theorem rationalOpen_comp (n : ℕ) {V : M9StandaloneDraft.Schemes K}
    {M : M9StandaloneDraft.Presheaves K} (j : yoneda.obj V ⟶ M)
    (hj : M9StandaloneDraft.DenseOpen K j)
    (h : M9StandaloneDraft.RationalOpen K n (yoneda.obj V)) :
    M9StandaloneDraft.RationalOpen K n M := by
  obtain ⟨U, i, hU, hi, a, ha, had, hbase⟩ := h
  exact ⟨U, i ≫ j, hU, denseOpen_comp K i j hi hj, a, ha, had, hbase⟩

end M9Native.StandaloneRationalOpenComposition

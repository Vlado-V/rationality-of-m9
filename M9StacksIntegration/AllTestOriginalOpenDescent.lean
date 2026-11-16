module

public import M9StacksIntegration.AllTestOriginalMonoFlatDescent
public import M9StacksIntegration.AllTestSingleFppfLift
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcOpenImmersion

/-!
# Genuine open-immersion descent on all original scheme tests

A represented open pullback over one actual locally surjective scheme chart
proves the full original relative open-immersion property. Representability
of arbitrary original pullbacks is derived by actual monomorphic flat-chart
descent, rather than supplied as an extra conclusion-shaped premise.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.AllTestOriginalOpenDescent
open AllTestBoundedCharts AllTestLargeSpaceSmallSections AllTestLargeSpaceGeometry

variable (K : Type u) [Field K]

/-- Small-valued full-original-test monomorphic flat-chart descent, with
the native site chosen internally from the actual three original schemes. -/
theorem isRepresentable_of_single_flat_chart
    {A : M9StandaloneDraft.Presheaves K}
    (hA : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) A)
    (T U R : M9StandaloneDraft.Schemes K) (q : U ⟶ T) (r : R ⟶ U)
    (f : A ⟶ yoneda.obj T) (a : yoneda.obj R ⟶ A)
    (h : IsPullback a (yoneda.map r) f (yoneda.map q))
    (hqf : Flat q.left) (hqp : LocallyOfFinitePresentation q.left)
    (hqs : Surjective q.left) (hrm : Mono r.left) (hrl : LocallyOfFiniteType r.left) :
    A.IsRepresentable := by
  rcases T with ⟨T, ⟨⟨⟩⟩, Thom⟩
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  rcases R with ⟨R, ⟨⟨⟩⟩, Rhom⟩
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({Spec (.of K), T, U, R} : Set Scheme.{u})
  let hK := hB (Spec (.of K)) (by simp)
  let Tn := siteObject B (Spec (.of K)) hK (hB T (by simp)) Thom
  let Un := siteObject B (Spec (.of K)) hK (hB U (by simp)) Uhom
  let Rn := siteObject B (Spec (.of K)) hK (hB R (by simp)) Rhom
  let qn : Un ⟶ Tn := boundedPreimage B K hK q
  let rn : Rn ⟶ Un := boundedPreimage B K hK r
  exact AllTestMonoFlatDescent.isRepresentable_of_single_flat_chart
    K B hK hA Tn Un Rn qn rn f a h hqf hqp hqs hrm hrl

/-- Actual local surjectivity is preserved by the genuine value-universe
lift; the original test objects and covering sieves are unchanged. -/
theorem valueLift_locallySurjective
    {F G : M9StandaloneDraft.Presheaves K} (a : F ⟶ G)
    (ha : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a) :
    Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) ((valueLift K).map a) := by
  letI := ha
  constructor
  intro T s
  refine (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).superset_covering ?_
    (Presheaf.imageSieve_mem _ a s.down)
  rintro W k ⟨t, ht⟩
  exact ⟨ULift.up t, congrArg ULift.up ht⟩

/-- A genuine represented monomorphic locally-finite-type pullback over an
actual original scheme atlas derives full-original representability; every
base-change-stable scheme property which descends fppf is transported too. -/
theorem presheafProperty_of_mono_lft_chart
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {F G : M9StandaloneDraft.Presheaves K}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) G)
    (f : F ⟶ G) (U V : M9StandaloneDraft.Schemes K)
    (a : yoneda.obj U ⟶ G)
    (ha : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a)
    (b : yoneda.obj V ⟶ F) (r : V ⟶ U)
    (h : IsPullback b (yoneda.map r) f a) [Mono r.left]
    [LocallyOfFiniteType r.left] (hr : P r.left) :
    (P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).presheaf f := by
  let J := Scheme.fppfTopology.over (M9StandaloneDraft.Base K)
  let FS : Sheaf J (Type u) := ⟨F, hF⟩
  let GS : Sheaf J (Type u) := ⟨G, hG⟩
  let W := valueLift K
  letI : W.Faithful := (valueLift_fullyFaithful K).faithful
  apply MorphismProperty.relative.of_exists
  intro T g
  let fS : FS ⟶ GS := ⟨f⟩
  let gS : J.yoneda.obj T ⟶ GS := ⟨g⟩
  let AS := pullback fS gS
  let p : AS.obj ⟶ F := (pullback.fst fS gS).hom
  let q : AS.obj ⟶ yoneda.obj T := (pullback.snd fS gS).hom
  have hp : IsPullback p q f g :=
    (IsPullback.of_hasPullback fS gS).map (sheafToPresheaf J (Type u))
  let Glarge : Sheaf J (Type (u+1)) :=
    (sheafCompose J uliftFunctor.{u+1, u}).obj GS
  obtain ⟨D, c, v, hcf, hcp, hcs, he⟩ :=
    AllTestSingleFppfLift.exists_single_fppf_lift K Glarge.property U T
      (W.map a) (valueLift_locallySurjective K a ha) (W.map g)
  have hev : yoneda.map v ≫ a = yoneda.map c ≫ g := by
    apply yonedaEquiv.injective
    exact congrArg (fun m => (m.app (op D) (ULift.up (𝟙 D))).down) he
  let R := pullback r v
  let k : R ⟶ V := pullback.fst r v
  let s : R ⟶ D := pullback.snd r v
  have hbase : IsPullback k s r v := IsPullback.of_hasPullback r v
  have hOuter : IsPullback (yoneda.map k ≫ b) (yoneda.map s) f (yoneda.map c ≫ g) := by
    simpa only [hev] using (hbase.map yoneda).paste_horiz h
  let α : yoneda.obj R ⟶ AS.obj := hp.lift
    (yoneda.map k ≫ b) (yoneda.map s ≫ yoneda.map c)
    (by simpa only [Category.assoc] using hOuter.w)
  have hαp : α ≫ p = yoneda.map k ≫ b := hp.lift_fst _ _ _
  have hαq : α ≫ q = yoneda.map s ≫ yoneda.map c := hp.lift_snd _ _ _
  have hChart : IsPullback α (yoneda.map s) q (yoneda.map c) := by
    have hO : IsPullback (α ≫ p) (yoneda.map s) f (yoneda.map c ≫ g) := by
      rw [hαp]
      exact hOuter
    exact hO.of_right hαq hp
  have hbaseS := hbase.map (Over.forget (M9StandaloneDraft.Base K))
  have hs : P s.left := MorphismProperty.of_isPullback hbaseS hr
  have hsm : Mono s.left := MorphismProperty.of_isPullback
    (P := MorphismProperty.monomorphisms Scheme.{u}) hbaseS
    (inferInstanceAs (Mono r.left))
  have hsl : LocallyOfFiniteType s.left := MorphismProperty.of_isPullback
    (P := @LocallyOfFiniteType.{u}) hbaseS
    (inferInstanceAs (LocallyOfFiniteType r.left))
  letI : AS.obj.IsRepresentable := isRepresentable_of_single_flat_chart
    K AS.property T D R c s q α hChart hcf hcp hcs hsm hsl
  let Z := AS.obj.reprX
  let e : yoneda.obj Z ≅ AS.obj := AS.obj.reprW
  let z : Z ⟶ T := yoneda.preimage (e.hom ≫ q)
  have hz : yoneda.map z = e.hom ≫ q := yoneda.map_preimage _
  let β : R ⟶ Z := yoneda.preimage (α ≫ e.inv)
  have hβ : yoneda.map β = α ≫ e.inv := yoneda.map_preimage _
  have hZChart : IsPullback (yoneda.map β) (yoneda.map s) (yoneda.map z) (yoneda.map c) := by
    apply hChart.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · simpa using hβ.symm
    · simp
    · simp [hz]
    · simp
  have hScheme := (hZChart.of_map_of_faithful yoneda).map
    (Over.forget (M9StandaloneDraft.Base K))
  have hzP : P z.left := MorphismProperty.of_isPullback_of_descendsAlong
    (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hScheme.flip
    (show (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) c.left from ⟨⟨hcs, hcf⟩, hcp⟩) hs
  have hZ : IsPullback (e.hom ≫ p) (yoneda.map z) f g := by
    apply hp.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simpa using hz.symm
    · simp
    · simp
  exact ⟨Z, e.hom ≫ p, z, hZ, hzP⟩

/-- In particular, genuine represented open pullback over an actual
original scheme atlas implies open immersion on EVERY original test. -/
theorem openImmersion_of_chart
    {F G : M9StandaloneDraft.Presheaves K}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) G)
    (f : F ⟶ G) (U V : M9StandaloneDraft.Schemes K)
    (a : yoneda.obj U ⟶ G)
    (ha : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a)
    (b : yoneda.obj V ⟶ F) (r : V ⟶ U)
    (h : IsPullback b (yoneda.map r) f a) [IsOpenImmersion r.left] :
    M9StandaloneDraft.OpenImmersion K f :=
  presheafProperty_of_mono_lft_chart K (@IsOpenImmersion.{u})
    hF hG f U V a ha b r h inferInstance

end M9StacksIntegration.AllTestOriginalOpenDescent

module

public import M9StacksIntegration.AllTestBoundedSpaceTargets
public import M9StacksIntegration.AllTestCoproductCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Small sections of actual large-value all-test spaces

An actual Type-(u+1) sheaf on the FULL original scheme category has Type-u
small sections if it has a relatively representable locally surjective atlas
from the universe-lifted Yoneda presheaf of an ORIGINAL Scheme.{u}.
The represented atlas pullback over each section maps monomorphically into
T × Z. An actual site containing T,Z,K bounds that pullback. The section is
then determined by its relation on a Type-u small model of that site.
No smallness, sheafification, classifier or family-equivalence premise is
supplied. The hypotheses are the actual atlas/sheaf conditions.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestLargeSpaceSmallSections
open AllTestBoundedCharts AllTestSheafCoproducts
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))
/-- The literal universe-lifted original Yoneda functor. -/
abbrev largeYoneda : M9StandaloneDraft.Schemes K ⥤
    (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1) := uliftYoneda.{u+1}
local notation "YL" => (largeYoneda K)

/-- The actual representing scheme of a large-value pullback of two bounded
original representables is bounded. The graph is a genuine scheme mono. -/
theorem represented_large_pullback_bounded
    {F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (U V : BigFppfOver B (Spec (.of K)) hK)
    (f : (YL).obj ((boundedInclusion B K hK).obj U) ⟶ F)
    (g : (YL).obj ((boundedInclusion B K hK).obj V) ⟶ F)
    (Z : M9StandaloneDraft.Schemes K)
    (s : Z ⟶ (boundedInclusion B K hK).obj V)
    (r : (YL).obj Z ⟶ (YL).obj ((boundedInclusion B K hK).obj U))
    (h : IsPullback r ((YL).map s) f g) : B.Contains Z.left := by
  let p : Z ⟶ (boundedInclusion B K hK).obj U := (YL).preimage r
  have hp : (YL).map p = r := (YL).map_preimage r
  have w : p.left ≫ ((boundedInclusion B K hK).obj U).hom =
      s.left ≫ ((boundedInclusion B K hK).obj V).hom := (Over.w p).trans (Over.w s).symm
  let t := pullback.lift p.left s.left w
  let : Mono t := by
    constructor
    intro W a b hab
    have ha : a ≫ p.left = b ≫ p.left := by
      simpa only [Category.assoc, t, pullback.lift_fst] using
        congrArg (fun m => m ≫ pullback.fst _ _) hab
    have hb : a ≫ s.left = b ≫ s.left := by
      simpa only [Category.assoc, t, pullback.lift_snd] using
        congrArg (fun m => m ≫ pullback.snd _ _) hab
    let Wk : M9StandaloneDraft.Schemes K := Over.mk (a ≫ Z.hom)
    let ak : Wk ⟶ Z := Over.homMk a rfl
    have hbbase : b ≫ Z.hom = a ≫ Z.hom := by
      calc
        b ≫ Z.hom = (b ≫ p.left) ≫ ((boundedInclusion B K hK).obj U).hom := by
          rw [Category.assoc, Over.w p]
        _ = (a ≫ p.left) ≫ ((boundedInclusion B K hK).obj U).hom := by rw [ha]
        _ = a ≫ Z.hom := by rw [Category.assoc, Over.w p]
    let bk : Wk ⟶ Z := Over.homMk b hbbase
    have hak : ak ≫ p = bk ≫ p := by ext; exact ha
    have hbk : ak ≫ s = bk ≫ s := by ext; exact hb
    have he : ak = bk := by
      apply (YL).map_injective
      apply h.hom_ext
      · simpa only [← hp, ← Functor.map_comp] using congrArg (fun m => (YL).map m) hak
      · simpa only [← Functor.map_comp] using congrArg (fun m => (YL).map m) hbk
    exact congrArg (fun m => m.left) he
  exact Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit t
    (Scheme.size_pullback_lt _ _ U.left.property V.left.property)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual atlas and the actual sheaf condition force small sections;
there is no assumed section-smallness or family-classification condition. -/
theorem small_obj_of_bounded_atlas
    (T Z : BigFppfOver B (Spec (.of K)) hK)
    (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F)
    (a : (YL).obj ((boundedInclusion B K hK).obj Z) ⟶ F)
    (ha : (YL).relativelyRepresentable a)
    (hloc : Presheaf.IsLocallySurjective (topology K) a) :
    Small.{u} (F.obj (op ((boundedInclusion B K hK).obj T))) := by
  classical
  let C := BigFppfOver B (Spec (.of K)) hK
  let : EssentiallySmall.{u} C := essentiallySmall_bigFppfOver B (Spec (.of K)) hK
  let e := equivSmallModel.{u} C
  let I := boundedInclusion B K hK
  let Code : Type u := Σ W : SmallModel.{u} C,
    (I.obj (e.inverse.obj W) ⟶ I.obj T) × (I.obj (e.inverse.obj W) ⟶ I.obj Z)
  let code : F.obj (op (I.obj T)) → Set Code := fun z c =>
    F.map c.2.1.op z = a.app (op (I.obj (e.inverse.obj c.1))) (ULift.up c.2.2)
  apply small_of_injective (f := code)
  intro z z' hcode
  let xz : (YL).obj (I.obj T) ⟶ F := uliftYonedaEquiv.{u+1}.symm z
  let xz' : (YL).obj (I.obj T) ⟶ F := uliftYonedaEquiv.{u+1}.symm z'
  obtain ⟨R, s, r, hR⟩ := ha xz
  have hRb := represented_large_pullback_bounded K B hK Z T a xz R s r hR
  rcases R with ⟨R, ⟨⟨⟩⟩, Rhom⟩
  let Rn := siteObject B (Spec (.of K)) hK hRb Rhom
  let W := e.functor.obj Rn
  let S := I.obj (e.inverse.obj W)
  let ε : Over.mk Rhom ≅ S := I.mapIso (e.unitIso.app Rn)
  let p : Over.mk Rhom ⟶ I.obj Z := (YL).preimage r
  have hp : (YL).map p = r := (YL).map_preimage r
  let sp : S ⟶ I.obj T := ε.inv ≫ s
  let pp : S ⟶ I.obj Z := ε.inv ≫ p
  have hS : IsPullback ((YL).map pp) ((YL).map sp) a xz := by
    apply hR.of_iso ((YL).mapIso ε) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · change r ≫ 𝟙 _ = (YL).map ε.hom ≫ (YL).map pp
      simp only [pp, ← Functor.map_comp, Iso.hom_inv_id_assoc, hp, Category.comp_id]
    · change (YL).map s ≫ 𝟙 _ = (YL).map ε.hom ≫ (YL).map sp
      simp only [sp, ← Functor.map_comp, Iso.hom_inv_id_assoc, Category.comp_id]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have hz : code z ⟨W, sp, pp⟩ := by
    have hv := congrArg (fun t : (YL).obj S ⟶ F => uliftYonedaEquiv.{u+1} t) hS.w
    change a.app (op S) (ULift.up ((𝟙 S) ≫ pp)) = F.map ((𝟙 S) ≫ sp).op z at hv
    simpa only [Category.id_comp] using hv.symm
  have hz' : code z' ⟨W, sp, pp⟩ := by rw [← hcode]; exact hz
  have hsec : F.map sp.op z = F.map sp.op z' := hz.trans hz'.symm
  have hpre : (YL).map sp ≫ xz = (YL).map sp ≫ xz' := by
    apply uliftYonedaEquiv.{u+1}.injective
    change F.map ((𝟙 S) ≫ sp).op z = F.map ((𝟙 S) ≫ sp).op z'
    simpa only [Category.id_comp] using hsec
  let J := topology K
  let Fs : Sheaf J (Type (u+1)) := ⟨F, hF⟩
  let qs : (J.uliftYoneda.{u+1}).obj S ⟶ (J.uliftYoneda.{u+1}).obj (I.obj T) :=
    (J.uliftYoneda.{u+1}).map sp
  let az : (J.uliftYoneda.{u+1}).obj (I.obj T) ⟶ Fs := ⟨xz⟩
  let az' : (J.uliftYoneda.{u+1}).obj (I.obj T) ⟶ Fs := ⟨xz'⟩
  let : Presheaf.IsLocallySurjective J a := hloc
  let : Presheaf.IsLocallySurjective J ((YL).map sp) :=
    Presheaf.isLocallySurjective_of_isPullback J hS.flip
  let : Sheaf.IsLocallySurjective qs :=
    inferInstanceAs (Presheaf.IsLocallySurjective J ((YL).map sp))
  have he : az = az' := (cancel_epi qs).mp (ObjectProperty.hom_ext _ hpre)
  have hx : xz = xz' := congrArg (fun t => t.hom) he
  exact uliftYonedaEquiv.{u+1}.symm.injective hx

/-- EVERY original test has small sections: the site used in the proof is
constructed from that test and the actual atlas, not assumed in the result. -/
theorem small_obj_of_atlas
    (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F) (Z : M9StandaloneDraft.Schemes K)
    (a : (YL).obj Z ⟶ F) (ha : (YL).relativelyRepresentable a)
    (hloc : Presheaf.IsLocallySurjective (topology K) a) (T : M9StandaloneDraft.Schemes K) :
    Small.{u} (F.obj (op T)) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({Spec (.of K), T.left, Z.left} : Set Scheme.{u})
  have hK := hB (Spec (.of K)) (by simp)
  have hT := hB T.left (by simp)
  have hZ := hB Z.left (by simp)
  rcases T with ⟨T, ⟨⟨⟩⟩, Thom⟩
  rcases Z with ⟨Z, ⟨⟨⟩⟩, Zhom⟩
  exact small_obj_of_bounded_atlas K B hK (siteObject B _ hK hT Thom)
    (siteObject B _ hK hZ Zhom) F hF a ha hloc

end M9StacksIntegration.AllTestLargeSpaceSmallSections

module

public import M9StacksIntegration.AllTestCoproductCartesian
public import M9StacksIntegration.StandaloneCurveCohomology

/-!
# The original curve predicate on a coproduct of schematic charts

All coproduct maps are genuine scheme maps over the original coefficient
field. Cartesian component squares are proved by the larger-universe Yoneda
coproduct theorem and reflected back to schemes. Properness, smooth relative
dimension and geometric connectedness are local on the actual target cover.
The original H1 genus condition is checked at every actual field-valued point.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestCurveCoproducts
open AllTestSheafCoproducts AllTestCoproductCartesian StandaloneCurveCohomology
universe u
variable (K : Type u) [Field K] {I : Type u}

abbrev sumArrow (Z U : I → M9StandaloneDraft.Schemes K) (q : ∀ i, Z i ⟶ U i) :=
  sumMap K Z (fun i => q i ≫ sumInclusion K U i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each actual component square of the original scheme coproduct map is
cartesian. No schematicity/classification premise is used. -/
theorem sumArrow_component_isPullback
    (Z U : I → M9StandaloneDraft.Schemes K) (q : ∀ i, Z i ⟶ U i) (i : I) :
    IsPullback (sumInclusion K Z i) (q i) (sumArrow K Z U q) (sumInclusion K U i) := by
  let J := topology K
  let Y := J.uliftYoneda.{u+1}
  let cZ := Cofan.mk (Y.obj (sumObject K Z)) fun i => Y.map (sumInclusion K Z i)
  let cU := Cofan.mk (Y.obj (sumObject K U)) fun i => Y.map (sumInclusion K U i)
  have hZ : IsColimit cZ := largeSumRepresentableIsColimit K Z
  have hU : IsVanKampenColimit cU :=
    Sheaf.isVanKampenColimit_of_isColimit_discrete J (largeSumRepresentableIsColimit K U)
  have hq (j : I) : cZ.inj j ≫ Y.map (sumArrow K Z U q) = Y.map (q j) ≫ cU.inj j := by
    change Y.map (sumInclusion K Z j) ≫ Y.map (sumArrow K Z U q) = _
    rw [← Y.map_comp, sumInclusion_sumMap, Y.map_comp]
    rfl
  apply IsPullback.of_map_of_faithful Y
  exact (hU cZ (Discrete.natTrans fun j => Y.map (q j.as)) (Y.map (sumArrow K Z U q))
    (NatTrans.ext (funext fun ⟨j⟩ => (hq j).symm)) (.of_discrete _)).mp ⟨hZ⟩ ⟨i⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Any scheme morphism property local on the target passes from the
original component maps to their actual coproduct map. -/
theorem morphismProperty_sumArrow
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (Z U : I → M9StandaloneDraft.Schemes K) (q : ∀ i, Z i ⟶ U i)
    (hq : ∀ i, P (q i).left) : P (sumArrow K Z U q).left := by
  apply IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover (fun i => (U i).left))
  intro i
  change I at i
  have hp : IsPullback (sumInclusion K Z i).left (q i).left
      (sumArrow K Z U q).left (sumInclusion K U i).left :=
    (sumArrow_component_isPullback K Z U q i).map
    (Over.forget (M9StandaloneDraft.Base K))
  change P (pullback.snd (sumArrow K Z U q).left (sumInclusion K U i).left)
  rw [← P.cancel_left_of_respectsIso hp.isoPullback.hom, hp.isoPullback_hom_snd]
  exact hq i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A coproduct of original proper smooth geometrically connected genus-g
scheme families is again the original scheme-curve predicate. This includes
its genuine H1 condition over EVERY field-valued point. -/
theorem schemeCurve_sumArrow
    (Z U : I → M9StandaloneDraft.Schemes K) (q : ∀ i, Z i ⟶ U i) (g : ℕ)
    (hq : ∀ i, M9StandaloneDraft.SchemeCurve (q i).left g) :
    M9StandaloneDraft.SchemeCurve (sumArrow K Z U q).left g := by
  letI : IsZariskiLocalAtTarget (@GeometricallyConnected.{u}) := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  have hp : IsProper (sumArrow K Z U q).left :=
    morphismProperty_sumArrow K (@IsProper) Z U q (fun i => (hq i).1)
  have hs : SmoothOfRelativeDimension 1 (sumArrow K Z U q).left :=
    morphismProperty_sumArrow K (@SmoothOfRelativeDimension 1) Z U q (fun i => (hq i).2.1)
  have hc : GeometricallyConnected (sumArrow K Z U q).left :=
    morphismProperty_sumArrow K (@GeometricallyConnected) Z U q (fun i => (hq i).2.2.1)
  letI := hp
  letI := hs
  letI := hc
  refine ⟨hp, hs, hc, ?_⟩
  intro L _ s
  refine ⟨finite_standalone_H1 (pullback.snd (sumArrow K Z U q).left s), ?_⟩
  let x : Spec (.of L) := Classical.choice inferInstance
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun i => (U i).left)).exists_eq (s x)
  change I at i
  change (U i).left at y
  change (sumInclusion K U i).left y = s x at hy
  letI : IsOpenImmersion (sumInclusion K U i).left := by
    change IsOpenImmersion (Sigma.ι (fun j => (U j).left) i)
    infer_instance
  have hsub : Set.range s ⊆ Set.range (sumInclusion K U i).left := by
    rintro _ ⟨z, rfl⟩
    exact ⟨y, hy.trans (congrArg s (Subsingleton.elim x z))⟩
  let a : Spec (.of L) ⟶ (U i).left :=
    IsOpenImmersion.lift (sumInclusion K U i).left s hsub
  have ha : a ≫ (sumInclusion K U i).left = s :=
    IsOpenImmersion.lift_fac _ _ hsub
  have hpbi : IsPullback (sumInclusion K Z i).left (q i).left
      (sumArrow K Z U q).left (sumInclusion K U i).left :=
    (sumArrow_component_isPullback K Z U q i).map
    (Over.forget (M9StandaloneDraft.Base K))
  have houter := (IsPullback.of_hasPullback (q i).left a).paste_horiz hpbi
  rw [ha] at houter
  let e := houter.isoPullback
  have he : e.hom ≫ pullback.snd (sumArrow K Z U q).left s = pullback.snd (q i).left a :=
    houter.isoPullback_hom_snd
  have hecart : IsPullback e.hom (pullback.snd (q i).left a)
      (pullback.snd (sumArrow K Z U q).left s)
      (Spec.map (CommRingCat.ofHom (algebraMap L L))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  exact (finrank_H1_fieldBaseChange L L e.hom _ _ hecart).symm.trans ((hq i).2.2.2 L a).2

end M9StacksIntegration.AllTestCurveCoproducts

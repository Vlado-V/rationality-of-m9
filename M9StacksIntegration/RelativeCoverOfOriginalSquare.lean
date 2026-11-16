module

public import M9StacksIntegration.RelativeCoverSchemeEvaluation
public import M9StacksIntegration.CurveClassifierPullback

/-! An actual original Cartesian source square and original cover map
construct the native relative morphism. Its chosen native source is
canonically the same original curve, preserving projection and evaluation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace M9Native.RelativeCoverOfOriginalSquare

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z X Q Y C : BigFppfOver B S hS}
  (z : Z ⟶ Q) (x : X ⟶ Q) (y : Y ⟶ Q)
  (r : C ⟶ Z) (f : C ⟶ Y) (sq : IsPullback r f z y)
  (g : C ⟶ X) (hg : g ≫ x = f ≫ y)

include hg

/-- The original cover, expressed on its actual native source square. -/
def relativeMorphism : RelativeMorphism B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
    (yoneda.map z) (yoneda.map x) (yoneda.obj Y) where
  base := yoneda.map y
  morphism := (sq.map yoneda).flip.isoPullback.inv ≫ yoneda.map g
  commutes := by
    let e := (sq.map yoneda).flip.isoPullback
    have hf : e.inv ≫ yoneda.map f = pullback.fst (yoneda.map y) (yoneda.map z) := by
      calc
        _ = e.inv ≫ (e.hom ≫ pullback.fst (yoneda.map y) (yoneda.map z)) :=
          congrArg (fun a => e.inv ≫ a) (sq.map yoneda).flip.isoPullback_hom_fst.symm
        _ = _ := by simp only [Iso.inv_hom_id_assoc]
    change (e.inv ≫ yoneda.map g) ≫ yoneda.map x = _
    calc
      _ = e.inv ≫ yoneda.map (g ≫ x) := by rw [Functor.map_comp, Category.assoc]
      _ = e.inv ≫ yoneda.map (f ≫ y) := congrArg (fun a => e.inv ≫ yoneda.map a) hg
      _ = (e.inv ≫ yoneda.map f) ≫ yoneda.map y := by rw [Functor.map_comp, Category.assoc]
      _ = pullback.fst (yoneda.map y) (yoneda.map z) ≫ yoneda.map y :=
        congrArg (fun a => a ≫ yoneda.map y) hf
      _ = _ := pullback.condition

variable (hz : yoneda.relativelyRepresentable (yoneda.map z))

/-- The actual chosen original-site source has the same source square. -/
theorem chosenSquare :
    IsPullback
      (RelativeCoverSchemeEvaluation.toOriginal z x (relativeMorphism z x y r f sq g hg) hz)
      (RelativeCoverSchemeEvaluation.projection z x (relativeMorphism z x y r f sq g hg) hz)
      z y := by
  simpa only [RelativeCoverSchemeEvaluation.base, relativeMorphism, Functor.preimage_map] using
    RelativeCoverSchemeEvaluation.sourceSquare z x (relativeMorphism z x y r f sq g hg) hz

/-- No physical source isomorphism is assumed: it follows from the two
actual Cartesian squares over the same actual base map. -/
def sourceIso : C ≅ RelativeCoverSchemeEvaluation.source z x (relativeMorphism z x y r f sq g hg) hz :=
  sq.isoIsPullback _ _ (chosenSquare z x y r f sq g hg hz)

theorem sourceIso_projection :
    (sourceIso z x y r f sq g hg hz).hom ≫
      RelativeCoverSchemeEvaluation.projection z x (relativeMorphism z x y r f sq g hg) hz = f :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

theorem sourceIso_toOriginal :
    (sourceIso z x y r f sq g hg hz).hom ≫
      RelativeCoverSchemeEvaluation.toOriginal z x (relativeMorphism z x y r f sq g hg) hz = r :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The canonical comparison preserves the ORIGINAL evaluation map. -/
theorem sourceIso_evaluation :
    (sourceIso z x y r f sq g hg hz).hom ≫
      RelativeCoverSchemeEvaluation.evaluation z x (relativeMorphism z x y r f sq g hg) hz = g := by
  let p := relativeMorphism z x y r f sq g hg
  let e := sourceIso z x y r f sq g hg hz
  have he : yoneda.map e.hom ≫ (hz.isPullback p.base).flip.isoPullback.hom =
      (sq.map yoneda).flip.isoPullback.hom := by
    change yoneda.map e.hom ≫ (hz.isPullback (yoneda.map y)).flip.isoPullback.hom =
      (sq.map yoneda).flip.isoPullback.hom
    apply pullback.hom_ext
    · rw [Category.assoc, (hz.isPullback (yoneda.map y)).flip.isoPullback_hom_fst,
        (sq.map yoneda).flip.isoPullback_hom_fst]
      change yoneda.map e.hom ≫ yoneda.map
        (RelativeCoverSchemeEvaluation.projection z x p hz) = yoneda.map f
      rw [← Functor.map_comp, sourceIso_projection]
    · rw [Category.assoc, (hz.isPullback (yoneda.map y)).flip.isoPullback_hom_snd,
        (sq.map yoneda).flip.isoPullback_hom_snd]
      simpa only [Functor.map_comp, RelativeCoverSchemeEvaluation.toOriginal,
        Functor.map_preimage] using congrArg (fun a => yoneda.map a)
          (sourceIso_toOriginal z x y r f sq g hg hz)
  apply yoneda.map_injective
  change yoneda.map (e.hom ≫ RelativeCoverSchemeEvaluation.evaluation z x p hz) = yoneda.map g
  rw [Functor.map_comp]
  simp only [RelativeCoverSchemeEvaluation.evaluation, RelativeCoverSchemeEvaluation.nativeEvaluation,
    Functor.map_preimage]
  rw [← Category.assoc, he]
  change (sq.map yoneda).flip.isoPullback.hom ≫
    ((sq.map yoneda).flip.isoPullback.inv ≫ yoneda.map g) = yoneda.map g
  simp only [Iso.hom_inv_id_assoc]

/-- The same derived isomorphism on the original schemes. -/
def originalSourceIso : (BigFppfOver.toScheme B S hS).obj C ≅
    (BigFppfOver.toScheme B S hS).obj
      (RelativeCoverSchemeEvaluation.source z x (relativeMorphism z x y r f sq g hg) hz) :=
  (BigFppfOver.toScheme B S hS).mapIso (sourceIso z x y r f sq g hg hz)

theorem originalSourceIso_projection :
    (originalSourceIso z x y r f sq g hg hz).hom ≫
      (BigFppfOver.toScheme B S hS).map
        (RelativeCoverSchemeEvaluation.projection z x (relativeMorphism z x y r f sq g hg) hz) =
      (BigFppfOver.toScheme B S hS).map f := by
  rw [originalSourceIso, Functor.mapIso_hom, ← Functor.map_comp, sourceIso_projection]

theorem originalSourceIso_evaluation :
    (originalSourceIso z x y r f sq g hg hz).hom ≫
      (BigFppfOver.toScheme B S hS).map
        (RelativeCoverSchemeEvaluation.evaluation z x (relativeMorphism z x y r f sq g hg) hz) =
      (BigFppfOver.toScheme B S hS).map g := by
  rw [originalSourceIso, Functor.mapIso_hom, ← Functor.map_comp, sourceIso_evaluation]

end Site

section Original

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {C Z T Y : Scheme.{u}} (hC : B.Contains C) (hSource : B.Contains Z)
  (hT : B.Contains T) (hY : B.Contains Y)
  (r : C ⟶ Z) (f : C ⟶ Y) (z : Z ⟶ T) (y : Y ⟶ T)

/-- An ORIGINAL Cartesian square supplies the genuine native site square.
The actual family maps are constructed by the integer-site functor. -/
theorem integerSiteSquare (sq : IsPullback r f z y) :
    IsPullback (integerSiteMap B hZ hC hSource r) (integerSiteMap B hZ hC hY f)
      (integerSiteMap B hZ hSource hT z) (integerSiteMap B hZ hY hT y) := by
  apply IsPullback.of_map_of_faithful (schemeSpaceFunctor B integerBase hZ)
  exact isPullback_schemeSpaceMap_integerSiteMap sq

end Original

section RepresentingLocus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (P : Subfunctor F) {Q Y W : BigFppfOver B S hS}
  (π : F ⟶ yoneda.obj Q) (A : yoneda.obj Y ⟶ P.toFunctor) [IsIso A]
  (q : Y ⟶ Q) (ha : (A ≫ P.ι) ≫ π = yoneda.map q)

include ha in
/-- An actual native section in a genuinely represented locus lifts to
an actual parameter point, preserving its SAME original base map. -/
theorem exists_parameter_point (s : F.obj (Opposite.op W))
    (hs : s ∈ P.obj (Opposite.op W)) :
    ∃ w : W ⟶ Y, A.app (Opposite.op W) w = ⟨s,hs⟩ ∧
      w ≫ q = π.app (Opposite.op W) s := by
  obtain ⟨w,hw⟩ := (ConcreteCategory.bijective_of_isIso (A.app (Opposite.op W))).2 ⟨s,hs⟩
  refine ⟨w,hw,?_⟩
  have h := congrArg (fun v : yoneda.obj Y ⟶ yoneda.obj Q => v.app (Opposite.op W) w) ha
  change π.app (Opposite.op W) (A.app (Opposite.op W) w).val = w ≫ q at h
  rw [hw] at h
  exact h.symm

end RepresentingLocus

end M9Native.RelativeCoverOfOriginalSquare
end

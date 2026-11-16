module

public import M9StacksIntegration.StandaloneModuliDraft
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Over

/-! Transport on the full original test category along an actual coefficient-base
isomorphism. All underlying schemes and scheme maps are unchanged. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.StandaloneCoefficientFamilyTransport

variable {K L : Type u} [Field K] [Field L]
    (e : Spec (.of K) ≅ Spec (.of L))

abbrev forward : M9StandaloneDraft.Schemes K ⥤ M9StandaloneDraft.Schemes L := Over.map e.hom
abbrev backward : M9StandaloneDraft.Schemes L ⥤ M9StandaloneDraft.Schemes K := Over.map e.inv

theorem forward_backward : forward e ⋙ backward e = 𝟭 _ := by
  rw [← Over.mapComp_eq, e.hom_inv_id, Over.mapId_eq]

theorem backward_forward : backward e ⋙ forward e = 𝟭 _ := by
  rw [← Over.mapComp_eq, e.inv_hom_id, Over.mapId_eq]

@[simp] theorem forward_obj_left (T : M9StandaloneDraft.Schemes K) :
    ((forward e).obj T).left = T.left := rfl

@[simp] theorem forward_map_left {T U : M9StandaloneDraft.Schemes K} (a : T ⟶ U) :
    ((forward e).map a).left = a.left := rfl

abbrev sliceUnitIso (T : M9StandaloneDraft.Schemes K) :
    T ≅ (backward e).obj ((forward e).obj T) := (Over.mapIso e).unitIso.app T

abbrev sliceCounitIso (T : M9StandaloneDraft.Schemes L) :
    (forward e).obj ((backward e).obj T) ≅ T := (Over.mapIso e).counitIso.app T

@[simp] theorem sliceUnitIso_hom_left (T : M9StandaloneDraft.Schemes K) :
    (sliceUnitIso e T).hom.left = 𝟙 T.left := rfl

@[simp] theorem sliceCounitIso_hom_left (T : M9StandaloneDraft.Schemes L) :
    (sliceCounitIso e T).hom.left = 𝟙 T.left := rfl

@[simp] theorem sliceUnitIso_inv_left (T : M9StandaloneDraft.Schemes K) :
    (sliceUnitIso e T).inv.left = 𝟙 T.left := rfl

@[simp] theorem sliceCounitIso_inv_left (T : M9StandaloneDraft.Schemes L) :
    (sliceCounitIso e T).inv.left = 𝟙 T.left := rfl

def presheafEquivalence : M9StandaloneDraft.Presheaves K ≌ M9StandaloneDraft.Presheaves L :=
  Equivalence.congrLeft (Over.mapIso e).op

abbrev presheafForwardFunctor :
    M9StandaloneDraft.Presheaves K ⥤ M9StandaloneDraft.Presheaves L :=
  (presheafEquivalence e).functor

abbrev presheafForward (F : M9StandaloneDraft.Presheaves K) :
    M9StandaloneDraft.Presheaves L := (presheafForwardFunctor e).obj F

theorem presheafForward_eq (F : M9StandaloneDraft.Presheaves K) :
    presheafForward e F = (backward e).op ⋙ F := rfl

abbrev presheafForwardMap {F G : M9StandaloneDraft.Presheaves K} (a : F ⟶ G) :
    presheafForward e F ⟶ presheafForward e G := (presheafForwardFunctor e).map a

/-- The represented comparison retains the literal original scheme map. -/
def yonedaForwardIso (T : M9StandaloneDraft.Schemes K) :
    presheafForward e (yoneda.obj T) ≅ yoneda.obj ((forward e).obj T) :=
  NatIso.ofComponents (fun U =>
    (Equiv.toIso (show (((backward e).obj U.unop ⟶ T) ≃
        (U.unop ⟶ (forward e).obj T)) from
      { toFun := fun a => Over.homMk a.left (by
          change a.left ≫ (T.hom ≫ e.hom) = U.unop.hom
          have h : a.left ≫ T.hom = U.unop.hom ≫ e.inv := Over.w a
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        invFun := fun a => Over.homMk a.left (by
          change a.left ≫ T.hom = U.unop.hom ≫ e.inv
          have h : a.left ≫ (T.hom ≫ e.hom) = U.unop.hom := Over.w a
          have h' := congrArg (fun q => q ≫ e.inv) h
          simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h')
        left_inv := fun a => Over.OverMorphism.ext rfl
        right_inv := fun a => Over.OverMorphism.ext rfl }))) (by
    intro U V a
    ext b
    apply Over.OverMorphism.ext
    rfl)

@[reassoc] theorem yonedaForwardIso_naturality
    {T U : M9StandaloneDraft.Schemes K} (a : T ⟶ U) :
    presheafForwardMap e (yoneda.map a) ≫ (yonedaForwardIso e U).hom =
      (yonedaForwardIso e T).hom ≫ yoneda.map ((forward e).map a) := by
  ext V b
  apply Over.OverMorphism.ext
  rfl

@[simp] theorem yonedaForwardIso_hom_app_left (T : M9StandaloneDraft.Schemes K)
    (U : M9StandaloneDraft.Schemes L) (a : (backward e).obj U ⟶ T) :
    ((yonedaForwardIso e T).hom.app (op U) a).left = a.left := rfl

@[simp] theorem yonedaForwardIso_inv_app_left (T : M9StandaloneDraft.Schemes K)
    (U : M9StandaloneDraft.Schemes L) (a : U ⟶ (forward e).obj T) :
    ((yonedaForwardIso e T).inv.app (op U) a).left = a.left := rfl

def testYonedaIso (T : M9StandaloneDraft.Schemes L) :
    presheafForward e (yoneda.obj ((backward e).obj T)) ≅ yoneda.obj T :=
  yonedaForwardIso e ((backward e).obj T) ≪≫ yoneda.mapIso (sliceCounitIso e T)

/-- Whiskering retains actual represented pullback squares. -/
theorem representedPullback_forward
    {F G : M9StandaloneDraft.Presheaves K} {T Z : M9StandaloneDraft.Schemes K}
    (r : yoneda.obj Z ⟶ F) (q : Z ⟶ T) (p : F ⟶ G) (v : yoneda.obj T ⟶ G)
    (h : IsPullback r (yoneda.map q) p v) :
    IsPullback ((yonedaForwardIso e Z).inv ≫ presheafForwardMap e r)
      (yoneda.map ((forward e).map q)) (presheafForwardMap e p)
      ((yonedaForwardIso e T).inv ≫ presheafForwardMap e v) := by
  apply (h.map (presheafForwardFunctor e)).of_iso'
    (yonedaForwardIso e Z).symm (Iso.refl _) (yonedaForwardIso e T).symm (Iso.refl _)
  · simp
  · change (yonedaForwardIso e Z).inv ≫ presheafForwardMap e (yoneda.map q) =
      yoneda.map ((forward e).map q) ≫ (yonedaForwardIso e T).inv
    apply (cancel_mono (yonedaForwardIso e T).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [yonedaForwardIso_naturality]
    simp
  · simp
  · simp

/-- Every represented morphism property is transported on all original tests.
The same physical scheme maps are used to check the property. -/
theorem presheafProperty_forward (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : M9StandaloneDraft.Presheaves K} (p : F ⟶ G)
    (hp : (P.inverseImage (Over.forget (Spec (.of K)))).presheaf p) :
    (P.inverseImage (Over.forget (Spec (.of L)))).presheaf (presheafForwardMap e p) := by
  apply MorphismProperty.relative.of_exists
  intro T v
  let vK : yoneda.obj ((backward e).obj T) ⟶ G :=
    (presheafForwardFunctor e).preimage ((testYonedaIso e T).hom ≫ v)
  let Z := hp.rep.pullback vK
  let q := hp.rep.snd vK
  let r := hp.rep.fst vK
  let qL := (forward e).map q ≫ (sliceCounitIso e T).hom
  refine ⟨(forward e).obj Z, (yonedaForwardIso e Z).inv ≫ presheafForwardMap e r,
    qL, ?_, ?_⟩
  · apply (representedPullback_forward e r q p vK (hp.rep.isPullback vK)).of_iso'
      (Iso.refl _) (Iso.refl _) ((yoneda.mapIso (sliceCounitIso e T)).symm) (Iso.refl _)
    · rfl
    · simp only [qL, Functor.map_comp, Iso.symm_hom, Functor.mapIso_inv,
        Iso.refl_hom, Category.id_comp]
      simp
    · simp
    · change (yoneda.map (sliceCounitIso e T).inv ≫
        (yonedaForwardIso e ((backward e).obj T)).inv) ≫ presheafForwardMap e vK = v
      have hv : presheafForwardMap e vK = (testYonedaIso e T).hom ≫ v :=
        (presheafForwardFunctor e).map_preimage _
      rw [hv]
      change (testYonedaIso e T).inv ≫ ((testYonedaIso e T).hom ≫ v) = v
      simp
  · change P qL.left
    have hq : P q.left := hp.property_snd vK
    have he : qL.left = q.left := by
      change q.left ≫ 𝟙 T.left = q.left
      exact Category.comp_id q.left
    exact he.symm ▸ hq

theorem presheafProperty_forward_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : M9StandaloneDraft.Presheaves K} (p : F ⟶ G) :
    (P.inverseImage (Over.forget (Spec (.of L)))).presheaf (presheafForwardMap e p) ↔
      (P.inverseImage (Over.forget (Spec (.of K)))).presheaf p := by
  constructor
  · intro h
    have hb := presheafProperty_forward e.symm P (presheafForwardMap e p) h
    let a : Arrow.mk p ≅ Arrow.mk (presheafForwardMap e.symm (presheafForwardMap e p)) :=
      Arrow.isoMk ((presheafEquivalence e).unitIso.app F)
        ((presheafEquivalence e).unitIso.app G) (by
          exact ((presheafEquivalence e).unitIso.hom.naturality p).symm)
    exact ((P.inverseImage (Over.forget (Spec (.of K)))).presheaf.arrow_mk_iso_iff a).mpr hb
  · exact presheafProperty_forward e P p

theorem relativelyRepresentable_forward
    {F G : M9StandaloneDraft.Presheaves K} (p : F ⟶ G)
    (hp : yoneda.relativelyRepresentable p) :
    yoneda.relativelyRepresentable (presheafForwardMap e p) := by
  exact (presheafProperty_forward e (⊤ : MorphismProperty Scheme.{u}) p
    ⟨hp, fun _ _ _ _ _ _ => trivial⟩).1

/-- The actual comparison of the transported diagonal with the diagonal
of the transported presheaf, also used for separatedness. -/
def diagonalForwardArrowIso (F : M9StandaloneDraft.Presheaves K) :
    Arrow.mk (presheafForwardMap e (diag F)) ≅ Arrow.mk (diag (presheafForward e F)) :=
  Arrow.isoMk (Iso.refl _) (asIso (prodComparison (presheafForwardFunctor e) F F)) (by
    change diag (presheafForward e F) =
      presheafForwardMap e (diag F) ≫ prodComparison (presheafForwardFunctor e) F F
    apply prod.hom_ext
    · rw [Category.assoc, prodComparison_fst, ← Functor.map_comp]
      simp [diag]
    · rw [Category.assoc, prodComparison_snd, ← Functor.map_comp]
      simp [diag])

/-- A genuine algebraic space on all original tests retains sheafness,
representable diagonal and a genuine surjective étale scheme atlas. -/
def spaceForward (M : M9StandaloneDraft.Space K) : M9StandaloneDraft.Space L where
  obj := presheafForward e M.obj
  isSheaf := (backward e).op_comp_isSheaf_of_isSheaf
    (Scheme.fppfTopology.over (Spec (.of L)))
    (Scheme.fppfTopology.over (Spec (.of K))) M.obj M.isSheaf
  diagonal := by
    have h := relativelyRepresentable_forward e (diag M.obj) M.diagonal
    exact (yoneda.relativelyRepresentable.arrow_mk_iso_iff (diagonalForwardArrowIso e M.obj)).mp h
  atlas := by
    obtain ⟨U, a, he, hs⟩ := M.atlas
    let aL := (yonedaForwardIso e U).inv ≫ presheafForwardMap e a
    have ea : Arrow.mk aL ≅ Arrow.mk (presheafForwardMap e a) :=
      Arrow.isoMk (yonedaForwardIso e U).symm (Iso.refl _) (by simp [aL])
    exact ⟨(forward e).obj U, aL,
      ((MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget (Spec (.of L)))).presheaf.arrow_mk_iso_iff ea).mpr
          (presheafProperty_forward e (@Etale.{u}) a he),
      ((MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget (Spec (.of L)))).presheaf.arrow_mk_iso_iff ea).mpr
          (presheafProperty_forward e (@Surjective.{u}) a hs)⟩

abbrev spaceBackward (M : M9StandaloneDraft.Space L) : M9StandaloneDraft.Space K :=
  spaceForward e.symm M

def spaceUnitIso (M : M9StandaloneDraft.Space K) :
    M.obj ≅ (spaceBackward e (spaceForward e M)).obj :=
  (presheafEquivalence e).unitIso.app M.obj

def spaceCounitIso (M : M9StandaloneDraft.Space L) :
    (spaceForward e (spaceBackward e M)).obj ≅ M.obj :=
  (presheafEquivalence e).counitIso.app M.obj

end M9Native.StandaloneCoefficientFamilyTransport

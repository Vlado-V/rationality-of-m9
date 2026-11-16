module

public import M9StacksIntegration.StandaloneCoefficientSpaceTransport
public import M9StacksIntegration.AllTestOriginalFamilyCategory

/-! Genuine coefficient transport of the original all-test family category.
The total algebraic space may be nonschematic. All chart maps and all of
their field fibres retain the same underlying scheme maps and genuine H1. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9StacksIntegration.AllTestOriginalFamilyCategory

universe u

namespace M9Native.StandaloneCoefficientFamilyTransport

variable {K L : Type u} [Field K] [Field L]
    (e : Spec (.of K) ≅ Spec (.of L))

/-- Original Cartesian family squares are transported over the exact
mapped base arrow. -/
theorem cartesianOver_forward
    {F G : M9StandaloneDraft.Presheaves K} {T U : M9StandaloneDraft.Schemes K}
    (r : F ⟶ G) (p : F ⟶ yoneda.obj T) (q : G ⟶ yoneda.obj U) (a : T ⟶ U)
    (h : IsPullback r p q (yoneda.map a)) :
    IsPullback (presheafForwardMap e r)
      (presheafForwardMap e p ≫ (yonedaForwardIso e T).hom)
      (presheafForwardMap e q ≫ (yonedaForwardIso e U).hom)
      (yoneda.map ((forward e).map a)) := by
  apply (h.map (presheafForwardFunctor e)).of_iso'
    (Iso.refl _) (Iso.refl _) (yonedaForwardIso e T).symm (yonedaForwardIso e U).symm
  · simp
  · simp [Category.assoc]
  · simp [Category.assoc]
  · change (yonedaForwardIso e T).inv ≫ presheafForwardMap e (yoneda.map a) =
      yoneda.map ((forward e).map a) ≫ (yonedaForwardIso e U).inv
    apply (Iso.eq_comp_inv (yonedaForwardIso e U)).mpr
    simp only [Category.assoc]
    rw [yonedaForwardIso_naturality]
    simp

/-- The actual local curve map is unchanged. -/
theorem schemeCurve_forward_iff {T Z : M9StandaloneDraft.Schemes K}
    (q : Z ⟶ T) (g : ℕ) :
    M9StandaloneDraft.SchemeCurve ((forward e).map q).left g ↔
      M9StandaloneDraft.SchemeCurve q.left g := Iff.rfl

/-- Every physical field fibre has literally the same original derived H1. -/
theorem fibre_H1_forward_eq {T Z : M9StandaloneDraft.Schemes K}
    (q : Z ⟶ T) (A : Type u) [Field A] (s : Spec (.of A) ⟶ T.left) :
    M9StandaloneDraft.H1 (pullback.snd ((forward e).map q).left s) =
      M9StandaloneDraft.H1 (pullback.snd q.left s) := rfl

/-- Transport an actual all-test family, retaining its nonschematic total
and deriving its actual local curve charts. -/
def familyForward {g : ℕ} (T : M9StandaloneDraft.Schemes K)
    (F : M9StandaloneDraft.Family K T g) :
    M9StandaloneDraft.Family L ((forward e).obj T) g where
  total := spaceForward e F.total
  projection := presheafForwardMap e F.projection ≫ (yonedaForwardIso e T).hom
  locally_curve := by
    intro t
    obtain ⟨T', Z, v, q, r, hv, ht, hcart, hq⟩ := F.locally_curve t
    refine ⟨(forward e).obj T', (forward e).obj Z, (forward e).map v, (forward e).map q,
      (yonedaForwardIso e Z).inv ≫ presheafForwardMap e r, hv, ht, ?_, hq⟩
    apply (cartesianOver_forward e r (yoneda.map q) F.projection v hcart).of_iso'
      (yonedaForwardIso e Z).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · change (yonedaForwardIso e Z).inv ≫
        (presheafForwardMap e (yoneda.map q) ≫ (yonedaForwardIso e T').hom) =
          yoneda.map ((forward e).map q)
      rw [yonedaForwardIso_naturality]
      simp
    · simp
    · simp

abbrev familyBackward {g : ℕ} (T : M9StandaloneDraft.Schemes L)
    (F : M9StandaloneDraft.Family L T g) :
    M9StandaloneDraft.Family K ((backward e).obj T) g := familyForward e.symm T F

@[simp] theorem familyForward_total_obj {g : ℕ} (T : M9StandaloneDraft.Schemes K)
    (F : M9StandaloneDraft.Family K T g) :
    (familyForward e T F).total.obj = presheafForward e F.total.obj := rfl

@[simp] theorem familyForward_projection {g : ℕ} (T : M9StandaloneDraft.Schemes K)
    (F : M9StandaloneDraft.Family K T g) :
    (familyForward e T F).projection =
      presheafForwardMap e F.projection ≫ (yonedaForwardIso e T).hom := rfl

/-- The actual functor on original Cartesian family arrows. -/
def curveFunctor (g : ℕ) : CurveObject K g ⥤ CurveObject L g where
  obj F := ⟨(forward e).obj F.base, familyForward e F.base F.family⟩
  map a :=
    { baseMap := (forward e).map a.baseMap
      totalMap := presheafForwardMap e a.totalMap
      cartesian := cartesianOver_forward e a.totalMap _ _ a.baseMap a.cartesian }
  map_id F := by
    apply CurveHom.ext
    · exact (forward e).map_id F.base
    · exact (presheafForwardFunctor e).map_id F.family.total.obj
  map_comp a b := by
    apply CurveHom.ext
    · exact (forward e).map_comp a.baseMap b.baseMap
    · exact (presheafForwardFunctor e).map_comp a.totalMap b.totalMap

theorem curveFunctor_projection (g : ℕ) :
    curveFunctor e g ⋙ projection L g = projection K g ⋙ forward e := rfl

theorem curveFunctor_totalFunctor (g : ℕ) :
    curveFunctor e g ⋙ totalFunctor L g =
      totalFunctor K g ⋙ presheafForwardFunctor e := rfl

/-- The represented unit comparison is pinned to the original slice unit. -/
theorem yoneda_unit_compat (T : M9StandaloneDraft.Schemes K) :
    ((presheafEquivalence e).unitIso.app (yoneda.obj T)).hom ≫
        presheafForwardMap e.symm (yonedaForwardIso e T).hom ≫
          (yonedaForwardIso e.symm ((forward e).obj T)).hom =
      yoneda.map (sliceUnitIso e T).hom := by
  ext U a
  apply Over.OverMorphism.ext
  change (𝟙 U.unop.left ≫ a.left) = a.left ≫ 𝟙 T.left
  simp

/-- The represented counit comparison is pinned to the original slice counit. -/
theorem yoneda_counit_compat (T : M9StandaloneDraft.Schemes L) :
    presheafForwardMap e (yonedaForwardIso e.symm T).hom ≫
        (yonedaForwardIso e ((backward e).obj T)).hom ≫
          yoneda.map (sliceCounitIso e T).hom =
      ((presheafEquivalence e).counitIso.app (yoneda.obj T)).hom := by
  ext U a
  apply Over.OverMorphism.ext
  change (a.left ≫ 𝟙 T.left) = 𝟙 U.unop.left ≫ a.left
  simp

theorem family_unit_projection {g : ℕ} (T : M9StandaloneDraft.Schemes K)
    (F : M9StandaloneDraft.Family K T g) :
    (spaceUnitIso e F.total).hom ≫
        (familyBackward e ((forward e).obj T) (familyForward e T F)).projection =
      F.projection ≫ yoneda.map (sliceUnitIso e T).hom := by
  ext U s
  apply Over.OverMorphism.ext
  change (F.projection.app (op ((backward e).obj ((forward e).obj U.unop)))
      (F.total.obj.map (sliceUnitIso e U.unop).inv.op s) |>.left) =
    (F.projection.app U s).left ≫ 𝟙 T.left
  have hn := F.projection.naturality_apply (sliceUnitIso e U.unop).inv.op s
  have hl := congrArg (fun a => a.left) hn
  change (F.projection.app (op ((backward e).obj ((forward e).obj U.unop)))
      (F.total.obj.map (sliceUnitIso e U.unop).inv.op s) |>.left) =
    𝟙 U.unop.left ≫ (F.projection.app U s).left at hl
  simpa only [Category.id_comp, Category.comp_id] using hl

theorem family_counit_projection {g : ℕ} (T : M9StandaloneDraft.Schemes L)
    (F : M9StandaloneDraft.Family L T g) :
    (spaceCounitIso e F.total).hom ≫ F.projection =
      (familyForward e ((backward e).obj T) (familyBackward e T F)).projection ≫
        yoneda.map (sliceCounitIso e T).hom := by
  ext U s
  apply Over.OverMorphism.ext
  change (F.projection.app U (F.total.obj.map (sliceCounitIso e U.unop).inv.op s)).left =
    (F.projection.app (op ((forward e).obj ((backward e).obj U.unop))) s).left ≫ 𝟙 T.left
  have hn := F.projection.naturality_apply (sliceCounitIso e U.unop).inv.op s
  have hl := congrArg (fun a => a.left) hn
  change (F.projection.app U (F.total.obj.map (sliceCounitIso e U.unop).inv.op s)).left =
    𝟙 U.unop.left ≫
      (F.projection.app (op ((forward e).obj ((backward e).obj U.unop))) s).left at hl
  simpa only [Category.id_comp, Category.comp_id] using hl

/-- A genuine original-family unit isomorphism over the actual slice unit.
Its Cartesian square and total-space isomorphism are derived. -/
def curveUnitIso (g : ℕ) :
    𝟭 (CurveObject K g) ≅ curveFunctor e g ⋙ curveFunctor e.symm g :=
  NatIso.ofComponents (fun F => isoMk K g (sliceUnitIso e F.base)
    (spaceUnitIso e F.family.total) (family_unit_projection e F.base F.family)) (by
    intro F G a
    apply CurveHom.ext
    · exact (Over.mapIso e).unitIso.hom.naturality a.baseMap
    · exact (presheafEquivalence e).unitIso.hom.naturality a.totalMap)

/-- A genuine original-family counit isomorphism over the actual slice counit. -/
def curveCounitIso (g : ℕ) :
    curveFunctor e.symm g ⋙ curveFunctor e g ≅ 𝟭 (CurveObject L g) :=
  NatIso.ofComponents (fun F => isoMk L g (sliceCounitIso e F.base)
    (spaceCounitIso e F.family.total) (family_counit_projection e F.base F.family)) (by
    intro F G a
    apply CurveHom.ext
    · exact (Over.mapIso e).counitIso.hom.naturality a.baseMap
    · exact (presheafEquivalence e).counitIso.hom.naturality a.totalMap)

/-- The actual all-original-test family categories are equivalent, including
nonschematic totals and their full Cartesian arrows. -/
def curveEquivalence (g : ℕ) : CurveObject K g ≌ CurveObject L g where
  functor := curveFunctor e g
  inverse := curveFunctor e.symm g
  unitIso := curveUnitIso e g
  counitIso := curveCounitIso e g
  functor_unitIso_comp F := by
    apply CurveHom.ext
    · exact (Over.mapIso e).functor_unitIso_comp F.base
    · exact (presheafEquivalence e).functor_unitIso_comp F.family.total.obj

/-- Same-base isomorphism of original families is preserved and reflected. -/
theorem familyIsomorphic_forward_iff {g : ℕ} (T : M9StandaloneDraft.Schemes K)
    (F G : M9StandaloneDraft.Family K T g) :
    M9StandaloneDraft.FamilyIsomorphic L (familyForward e T F) (familyForward e T G) ↔
      M9StandaloneDraft.FamilyIsomorphic K F G := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (presheafForwardFunctor e).preimageIso a
    refine ⟨b, ?_⟩
    apply (presheafForwardFunctor e).map_injective
    apply (Iso.cancel_iso_hom_right _ _ (yonedaForwardIso e T)).mp
    rw [Functor.map_comp]
    change (presheafForwardFunctor e).map b.hom ≫
      presheafForwardMap e G.projection ≫ (yonedaForwardIso e T).hom =
        presheafForwardMap e F.projection ≫ (yonedaForwardIso e T).hom
    have hb : (presheafForwardFunctor e).map b.hom = a.hom :=
      (presheafForwardFunctor e).map_preimage a.hom
    rw [hb]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨(presheafForwardFunctor e).mapIso a, ?_⟩
    change presheafForwardMap e a.hom ≫
      (presheafForwardMap e G.projection ≫ (yonedaForwardIso e T).hom) =
        presheafForwardMap e F.projection ≫ (yonedaForwardIso e T).hom
    rw [← Category.assoc, ← Functor.map_comp, ha]

end M9Native.StandaloneCoefficientFamilyTransport

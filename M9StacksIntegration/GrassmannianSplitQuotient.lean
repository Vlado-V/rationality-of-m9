module

public import M9StacksIntegration.GrassmannianFieldKernels

/-!
# Native Grassmannian quotients along an actual split free quotient

A split map of the actual free sheaves of ranks fourteen and thirteen
induces an equivalence between native rank-five quotient classes of the
smaller free sheaf and native rank-five quotients annihilating the
complementary projector of the larger free sheaf. No point or scheme is
replaced by its reduced structure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u
namespace M9Native.GrassmannianSplitQuotient
open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix

/-- An actual free-sheaf quotient with an actual right inverse. -/
structure SplitMap (T : Scheme.{u}) where
  quotient : F T 14 ⟶ F T 13
  splitting : F T 13 ⟶ F T 14
  split_identity : splitting ≫ quotient = 𝟙 _

variable {T : Scheme.{u}} (s : SplitMap T)

/-- The actual projector onto the discarded line. -/
def projector : F T 14 ⟶ F T 14 :=
  𝟙 _ - s.quotient ≫ s.splitting

/-- The original smaller free quotient map is genuinely an epimorphism. -/
theorem quotient_epi : Epi s.quotient :=
  epi_of_epi_fac s.split_identity

/-- The projector is killed by the split quotient. -/
theorem projector_quotient : projector s ≫ s.quotient = 0 := by
  rw [projector, Preadditive.sub_comp, Category.id_comp,
    Category.assoc, s.split_identity, Category.comp_id, sub_self]

/-- Projector annihilation is the exact actual factorization identity. -/
theorem projector_comp_eq_zero_iff {Q : T.Modules} (f : F T 14 ⟶ Q) :
    projector s ≫ f = 0 ↔ s.quotient ≫ (s.splitting ≫ f) = f := by
  rw [projector, Preadditive.sub_comp, Category.id_comp, sub_eq_zero]
  constructor
  · intro h
    simpa only [Category.assoc] using h.symm
  · intro h
    simpa only [Category.assoc] using h.symm

/-- Actual annihilation of the complementary projector by a native quotient. -/
def Kills (q : QuotientPresentation T 9 14) : Prop :=
  projector s ≫ q.map = 0

/-- Compose an actual rank-five quotient of free13 with the split map. -/
def lift (q : QuotientPresentation T 8 13) : QuotientPresentation T 9 14 := by
  letI : Epi s.quotient := quotient_epi s
  letI : Epi q.map := q.map_epi
  exact { target := q.target
          map := s.quotient ≫ q.map
          map_epi := inferInstance
          finiteLocallyFree := q.finiteLocallyFree }

theorem lift_kills (q : QuotientPresentation T 8 13) : Kills s (lift s q) := by
  change projector s ≫ (s.quotient ≫ q.map) = 0
  rw [← Category.assoc, projector_quotient, zero_comp]

/-- A quotient annihilating the projector descends by the actual section.
Its epimorphism property follows from the original quotient epimorphism. -/
def descend (q : QuotientPresentation T 9 14) (hq : Kills s q) :
    QuotientPresentation T 8 13 := by
  letI : Epi q.map := q.map_epi
  have hepi : Epi (s.splitting ≫ q.map) :=
    epi_of_epi_fac ((projector_comp_eq_zero_iff s q.map).mp hq)
  exact { target := q.target
          map := s.splitting ≫ q.map
          map_epi := hepi
          finiteLocallyFree := q.finiteLocallyFree }

theorem lift_respects_isomorphic {q q' : QuotientPresentation T 8 13}
    (h : q.Isomorphic q') : (lift s q).Isomorphic (lift s q') := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  change (s.quotient ≫ q.map) ≫ e.hom = s.quotient ≫ q'.map
  rw [Category.assoc, he]

theorem kills_iff_of_isomorphic {q q' : QuotientPresentation T 9 14}
    (h : q.Isomorphic q') : Kills s q ↔ Kills s q' := by
  obtain ⟨e, he⟩ := h
  constructor
  · intro hq
    change projector s ≫ q'.map = 0
    rw [← he, ← Category.assoc, hq, zero_comp]
  · intro hq
    apply (cancel_mono e.hom).1
    change (projector s ≫ q.map) ≫ e.hom = (0 : F T 14 ⟶ q.target) ≫ e.hom
    rw [Category.assoc, he, hq, zero_comp]

theorem descend_respects_isomorphic {q q' : QuotientPresentation T 9 14}
    (hq : Kills s q) (hq' : Kills s q') (h : q.Isomorphic q') :
    (descend s q hq).Isomorphic (descend s q' hq') := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  change (s.splitting ≫ q.map) ≫ e.hom = s.splitting ≫ q'.map
  rw [Category.assoc, he]

theorem descend_lift (q : QuotientPresentation T 8 13) :
    (descend s (lift s q) (lift_kills s q)).Isomorphic q := by
  refine ⟨Iso.refl _, ?_⟩
  change (s.splitting ≫ (s.quotient ≫ q.map)) ≫ 𝟙 _ = q.map
  rw [Category.comp_id, ← Category.assoc, s.split_identity, Category.id_comp]

theorem lift_descend (q : QuotientPresentation T 9 14) (hq : Kills s q) :
    (lift s (descend s q hq)).Isomorphic q := by
  refine ⟨Iso.refl _, ?_⟩
  change (s.quotient ≫ (s.splitting ≫ q.map)) ≫ 𝟙 _ = q.map
  rw [Category.comp_id]
  exact (projector_comp_eq_zero_iff s q.map).mp hq

/-- The actual annihilation predicate is well defined on native quotient classes. -/
def KillsPoint : Points T 9 14 → Prop :=
  Quotient.lift (Kills s) (by
    intro q q' h
    apply propext
    induction h with
    | rel _ _ h => exact kills_iff_of_isomorphic s h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h h' => exact h.trans h')

/-- Forward map on the original native quotient classes. -/
def liftPoints : Points T 8 13 → Points T 9 14 :=
  Quotient.lift (fun q => (⟦lift s q⟧ : Points T 9 14)) (by
    intro q q' h
    induction h with
    | rel _ _ h => exact Quotient.sound (Relation.EqvGen.rel _ _ (lift_respects_isomorphic s h))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h h' => exact h.trans h')

theorem liftPoints_kills (x : Points T 8 13) : KillsPoint s (liftPoints s x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact lift_kills s q

/-- The forward map lands in exactly the actual annihilation subfunctor. -/
def liftPoint (x : Points T 8 13) : {y : Points T 9 14 // KillsPoint s y} :=
  ⟨liftPoints s x, liftPoints_kills s x⟩

/-- Descent of an actual quotient class; a representative is used only to
construct the map, and its independence is proved below. -/
def descendPoint (y : {x : Points T 9 14 // KillsPoint s x}) : Points T 8 13 := by
  let q : QuotientPresentation T 9 14 := Quotient.out y.1
  have hq : Kills s q := by
    have h : KillsPoint s (⟦q⟧ : Points T 9 14) := by
      rw [show (⟦q⟧ : Points T 9 14) = y.1 from Quotient.out_eq y.1]
      exact y.2
    exact h
  exact ⟦descend s q hq⟧

theorem descendPoint_mk (q : QuotientPresentation T 9 14) (hq : Kills s q) :
    descendPoint s ⟨⟦q⟧, hq⟩ = ⟦descend s q hq⟧ := by
  change (⟦descend s (Quotient.out (⟦q⟧ : Points T 9 14)) _⟧ : Points T 8 13) = _
  apply Quotient.sound
  apply Relation.EqvGen.rel
  apply descend_respects_isomorphic
  exact GrassmannianFieldKernels.isomorphic_of_class_eq (Quotient.out_eq (⟦q⟧ : Points T 9 14))

theorem descendPoint_liftPoint (x : Points T 8 13) :
    descendPoint s (liftPoint s x) = x := by
  refine Quotient.inductionOn x fun q => ?_
  change descendPoint s ⟨⟦lift s q⟧, lift_kills s q⟩ = ⟦q⟧
  exact (descendPoint_mk s (lift s q) (lift_kills s q)).trans
    (Quotient.sound (Relation.EqvGen.rel _ _ (descend_lift s q)))

theorem liftPoint_descendPoint (y : {x : Points T 9 14 // KillsPoint s x}) :
    liftPoint s (descendPoint s y) = y := by
  apply Subtype.ext
  change (⟦lift s (descend s (Quotient.out y.1) _)⟧ : Points T 9 14) = y.1
  exact (Quotient.sound (Relation.EqvGen.rel _ _ (lift_descend s (Quotient.out y.1) _))).trans
    (Quotient.out_eq y.1)

/-- Native rank-five quotients of free13 classify exactly native rank-five
quotients of free14 which kill the discarded actual line projector. -/
def pointsEquiv : Points T 8 13 ≃ {x : Points T 9 14 // KillsPoint s x} where
  toFun := liftPoint s
  invFun := descendPoint s
  left_inv := descendPoint_liftPoint s
  right_inv := liftPoint_descendPoint s

theorem liftPoints_injective : Function.Injective (liftPoints s) := by
  intro x y h
  apply (pointsEquiv s).injective
  exact Subtype.ext h

theorem exists_liftPoints_iff (y : Points T 9 14) :
    (∃ x : Points T 8 13, liftPoints s x = y) ↔ KillsPoint s y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact liftPoints_kills s x
  · intro hy
    obtain ⟨x, hx⟩ := (pointsEquiv s).surjective ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Compatibility with arbitrary genuine pullback of quotient presentations.
The displayed square is the original free-sheaf pullback comparison. -/
theorem pullback_lift {S : Scheme.{u}} (f : S ⟶ T) (t : SplitMap S)
    (h : (pullbackFreeIso f 14).inv ≫ (Scheme.Modules.pullback f).map s.quotient =
      t.quotient ≫ (pullbackFreeIso f 13).inv)
    (q : QuotientPresentation T 8 13) :
    (pullbackPresentation f (lift s q)).Isomorphic
      (lift t (pullbackPresentation f q)) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((pullbackFreeIso f 14).inv ≫
    (Scheme.Modules.pullback f).map (s.quotient ≫ q.map)) ≫ 𝟙 _ =
      t.quotient ≫ ((pullbackFreeIso f 13).inv ≫ (Scheme.Modules.pullback f).map q.map)
  rw [Category.comp_id, Functor.map_comp, ← Category.assoc, h, Category.assoc]

/-- Naturality on the actual native quotient functors, without restricting test schemes. -/
theorem liftPoints_natural {S : Scheme.{u}} (f : S ⟶ T) (t : SplitMap S)
    (h : (pullbackFreeIso f 14).inv ≫ (Scheme.Modules.pullback f).map s.quotient =
      t.quotient ≫ (pullbackFreeIso f 13).inv)
    (x : Points T 8 13) :
    pullbackPointsMap f 9 14 (liftPoints s x) =
      liftPoints t (pullbackPointsMap f 8 13 x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (Relation.EqvGen.rel _ _ (pullback_lift s f t h q))

end M9Native.GrassmannianSplitQuotient

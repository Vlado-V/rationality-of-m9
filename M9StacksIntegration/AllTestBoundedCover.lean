module

public import M9StacksIntegration.AllTestBoundedCharts
public import StacksFrontier.AlgebraicGeometry.Size.Coverings

/-!
# A bounded actual étale covering for an all-test curve family

This is a cover-size step toward the family comparison. The actual covering
has small index, its coproduct has size at most the original base, and its
members carry the actual original schematic presentations of the family.
No native family/classifier or global schematic descent conclusion is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Cardinal TopologicalSpace

namespace M9StacksIntegration.AllTestBoundedCover

universe u v

theorem mk_sigma_fin_le {α : Type u} (n : α → ℕ) {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hα : #α ≤ κ) : #(Σ a : α, Fin (n a)) ≤ κ := by
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => (ℵ₀ : Cardinal.{0}))
    fun _ => Cardinal.mk_lt_aleph0.le).trans ?_
  rw [Cardinal.sum_const, Cardinal.lift_uzero, Cardinal.lift_aleph0]
  exact (mul_le_mul' hα hκ).trans_eq (Cardinal.mul_eq_self hκ)

/-- The native bounded-cover proof, with its actual étaleness retained.
The refinement is made of affine opens of the original cover members. -/
theorem exists_small_etale_refinement (T : Scheme.{u}) (C : FppfCovering.{v} T)
    (hC : ∀ i, Etale (C.f i)) :
    ∃ W : FppfCovering.{u} T,
      W.IsRefinement C ∧ (∀ i, Etale (W.f i)) ∧
        Cardinal.mk W.ι ≤ Scheme.size T ∧
        (∀ i, Scheme.size (W.X i) ≤ Scheme.size T) ∧
        Scheme.size (∐ W.X) ≤ Scheme.size T := by
  classical
  choose n a V hVaff hVcov using C.exists_finite_affineOpens_cover
  let W : FppfCovering.{u} T :=
    { ι := Σ U : T.affineOpens, Fin (n U)
      X := fun ⟨U, j⟩ => (V U j).toScheme
      f := fun ⟨U, j⟩ => (V U j).ι ≫ C.f (a U j)
      flat := fun ⟨U, j⟩ => by letI := hC (a U j); infer_instance
      lfp := fun ⟨U, j⟩ => by letI := hC (a U j); infer_instance
      jointly_surjective := by
        intro t
        obtain ⟨O, hO, htO, _⟩ :=
          Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens (Opens.mem_top t)
        have ht : t ∈ ⋃ j, C.f (a ⟨O, hO⟩ j) ''
            (V ⟨O, hO⟩ j : Set (C.X (a ⟨O, hO⟩ j))) := by
          rw [hVcov ⟨O, hO⟩]
          exact htO
        obtain ⟨j, x, hxV, hxt⟩ := Set.mem_iUnion.mp ht
        exact ⟨⟨⟨O, hO⟩, j⟩, ⟨x, hxV⟩, hxt⟩ }
  have hcard : Cardinal.mk W.ι ≤ Scheme.size T :=
    mk_sigma_fin_le n T.aleph0_le_size T.mk_affineOpens_le_size
  have hsize : ∀ i, Scheme.size (W.X i) ≤ Scheme.size T := by
    rintro ⟨U, j⟩
    letI := hC (a U j)
    letI : IsAffine (V U j).toScheme := hVaff U j
    exact Scheme.size_le_of_locallyOfFiniteType ((V U j).ι ≫ C.f (a U j))
  refine ⟨W, (fun ⟨U, j⟩ => ⟨a U j, (V U j).ι, rfl⟩), ?_, hcard, hsize, ?_⟩
  · rintro ⟨U, j⟩
    letI := hC (a U j)
    infer_instance
  · exact schemeSize_coproduct_le W.X (Scheme.size T) T.aleph0_le_size hcard hsize

/-- The bounded étale covering family has an actual bounded coproduct scheme
whose actual canonical map to the original base is étale and surjective. -/
theorem bounded_cover_coproduct (B : BigFppfSite.{u}) {T : Scheme.{u}}
    (hT : B.Contains T) (W : FppfCovering.{u} T) (hWet : ∀ j, Etale (W.f j))
    (hsize : Scheme.size (∐ W.X) ≤ Scheme.size T) :
    B.Contains (∐ W.X) ∧ Etale (Sigma.desc W.f) ∧ Surjective (Sigma.desc W.f) := by
  letI : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  refine ⟨hsize.trans_lt hT, IsZariskiLocalAtSource.sigmaDesc hWet, ?_⟩
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨j, x, hx⟩ := W.jointly_surjective t
  exact Set.mem_iUnion.mpr ⟨j, x, hx⟩

section Families

open AllTestBoundedCharts StandaloneCurveCohomology

variable (B : BigFppfSite.{u}) (K : Type u) [Field K]
  (hK : B.Contains (Spec (.of K)))

/-- An arbitrary standalone family over a bounded base has an actual étale
cover with bounded coproduct and actual bounded schematic curve presentations
on every member. The original presheaf and its projection remain in the
displayed cartesian squares. -/
theorem standaloneFamily_has_bounded_cover
    {T : M9StandaloneDraft.Schemes K} (hT : B.Contains T.left) {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) :
    ∃ W : FppfCovering.{u} T.left,
      (∀ j, Etale (W.f j)) ∧ Scheme.size (∐ W.X) ≤ Scheme.size T.left ∧
      ∀ j, ∃ (Z : M9StandaloneDraft.Schemes K)
        (q : Z ⟶ Over.mk (W.f j ≫ T.hom)) (r : yoneda.obj Z ⟶ F.total.obj),
        B.Contains (W.X j) ∧ B.Contains Z.left ∧
          IsPullback r (yoneda.map q) F.projection
            (yoneda.map (Over.homMk (W.f j) rfl : Over.mk (W.f j ≫ T.hom) ⟶ T)) ∧
          M9StandaloneDraft.SchemeCurve q.left g := by
  classical
  choose U Z v q r hv ht hcart hq using F.locally_curve
  let C : FppfCovering.{u} T.left :=
    { ι := T.left
      X := fun t => (U t).left
      f := fun t => (v t).left
      flat := fun t => by letI := hv t; infer_instance
      lfp := fun t => by letI := hv t; infer_instance
      jointly_surjective := fun t => ⟨t, (ht t).choose, (ht t).choose_spec⟩ }
  obtain ⟨W, href, hWet, _hcard, hWsize, htotal⟩ :=
    exists_small_etale_refinement T.left C hv
  refine ⟨W, hWet, htotal, ?_⟩
  intro j
  obtain ⟨t, b, hb⟩ := href j
  let A : M9StandaloneDraft.Schemes K := Over.mk (W.f j ≫ T.hom)
  let w : A ⟶ U t := Over.homMk b (by
    rw [← Over.w (v t), ← Category.assoc]
    exact congrArg (fun z => z ≫ T.hom) hb)
  let P := pullback (q t) w
  let p : P ⟶ A := pullback.snd (q t) w
  let a : P ⟶ Z t := pullback.fst (q t) w
  have hp : M9StandaloneDraft.SchemeCurve p.left g :=
    schemeCurve_of_isPullback (q t).left p.left a.left w.left
      ((IsPullback.of_hasPullback (q t) w).map (Over.forget (M9StandaloneDraft.Base K))) (hq t)
  have hA : B.Contains A.left := (hWsize j).trans_lt hT
  have hP : B.Contains P.left := contains_total_of_schemeCurve B K hA p.left hp
  have hbase : w ≫ v t = (Over.homMk (W.f j) rfl : A ⟶ T) := by
    ext
    exact hb
  refine ⟨P, p, yoneda.map a ≫ r t, hA, hP, ?_, hp⟩
  have hsmall := (IsPullback.of_hasPullback (q t) w).map yoneda
  have hwhole := hsmall.paste_horiz (hcart t)
  have hh : IsPullback (yoneda.map a ≫ r t) (yoneda.map p) F.projection
      (yoneda.map (w ≫ v t)) := by
    simpa only [Functor.map_comp] using hwhole
  rw [hbase] at hh
  exact hh

end Families

end M9StacksIntegration.AllTestBoundedCover

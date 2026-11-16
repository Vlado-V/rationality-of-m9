module

public import M9StacksIntegration.StandaloneCurveCohomology
public import M9StacksIntegration.AllTestSchemeFamilies
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Actual bounded charts for the unchanged all-test family

The constructions are isolated from the staged CoarseSiteComparison source.
The source and target test schemes and their original coefficient maps are
retained. Properness and finite-presentation size control supply bounded
schematic charts; there is no classifier or family-equivalence premise.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open M9StacksIntegration.StandaloneCurveCohomology

namespace M9StacksIntegration.AllTestBoundedCharts
universe u

section BoundedSchemes

variable (B : BigFppfSite.{u}) (K : Type u) [Field K]
  (hK : B.Contains (Spec (.of K)))

/-- The actual fully faithful inclusion of bounded test schemes among all test
schemes over the original field. Its object field retains the original map. -/
def boundedInclusion : BigFppfOver B (Spec (.of K)) hK ⥤ M9StandaloneDraft.Schemes K where
  obj T := Over.mk T.hom.hom
  map a := Over.homMk a.left.hom (congrArg (fun f => f.hom) (Over.w a))

instance boundedInclusion_faithful : (boundedInclusion B K hK).Faithful where
  map_injective {T U} a b hab := by
    ext
    exact congrArg (fun z => z.left) hab

/-- Lift an actual original scheme map between two bounded base objects. -/
def boundedPreimage {T U : BigFppfOver B (Spec (.of K)) hK}
    (a : (boundedInclusion B K hK).obj T ⟶ (boundedInclusion B K hK).obj U) : T ⟶ U :=
  Over.homMk (ObjectProperty.homMk a.left) (ObjectProperty.hom_ext _ (Over.w a))

instance boundedInclusion_full : (boundedInclusion B K hK).Full where
  map_surjective {T U} a := by
    exact ⟨boundedPreimage B K hK a, rfl⟩

/-- Every all-test scheme already belonging to the bounded site is the image
of its actual native site object; this is equality of original schemes/maps. -/
theorem boundedInclusion_siteObject (T : M9StandaloneDraft.Schemes K)
    (hT : B.Contains T.left) :
    (boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hT T.hom) = T := by
  cases T
  rfl

/-- Restricting the actual representable all-test presheaf recovers the actual
representable bounded presheaf, by full faithfulness of the inclusion. -/
def restrictRepresentableIso (T : BigFppfOver B (Spec (.of K)) hK) :
    (boundedInclusion B K hK).op ⋙ yoneda.obj ((boundedInclusion B K hK).obj T) ≅
      yoneda.obj T where
  hom :=
    { app := fun U => TypeCat.ofHom fun a =>
        boundedPreimage B K hK (T := U.unop) (U := T) a
      naturality := by
        intro U V a
        ext b
        rfl }
  inv :=
    { app := fun U => TypeCat.ofHom fun a => (boundedInclusion B K hK).map a
      naturality := by
        intro U V a
        ext b
        rfl }
  hom_inv_id := by
    ext U a
    rfl
  inv_hom_id := by
    ext U a
    rfl

/-- Proper smooth scheme families over a bounded base have bounded total
scheme automatically, by the native finite-type/quasi-compact size theorem. -/
theorem contains_total_of_schemeCurve {T : M9StandaloneDraft.Schemes K}
    (hT : B.Contains T.left) {Z : Scheme.{u}} (q : Z ⟶ T.left) {g : ℕ}
    (hq : M9StandaloneDraft.SchemeCurve q g) : B.Contains Z := by
  letI : IsProper q := hq.1
  letI : SmoothOfRelativeDimension 1 q := hq.2.1
  letI : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact q hT

/-- Any point of an arbitrary étale cover of a bounded base is covered by an
actual bounded affine scheme. This is the finite-presentation size step, not a
restriction of the standalone test quantifiers. -/
theorem exists_bounded_affine_etale_refinement
    {T T' : M9StandaloneDraft.Schemes K} (hT : B.Contains T.left)
    (v : T' ⟶ T) [Etale v.left] (t : T.left) (ht : t ∈ Set.range v.left) :
    ∃ (U : M9StandaloneDraft.Schemes K) (w : U ⟶ T'),
      IsAffine U.left ∧ B.Contains U.left ∧ IsOpenImmersion w.left ∧
        Etale (w ≫ v).left ∧ t ∈ Set.range (w ≫ v).left := by
  obtain ⟨x, hx⟩ := ht
  obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := T'.left) (x := x) (U := ⊤) (show x ∈ (⊤ : T'.left.Opens) from trivial)
  let U : M9StandaloneDraft.Schemes K := Over.mk (W.ι ≫ T'.hom)
  let w : U ⟶ T' := Over.homMk W.ι rfl
  letI : IsAffine U.left := hW
  letI : IsOpenImmersion w.left := by
    change IsOpenImmersion W.ι
    infer_instance
  letI : Etale (w ≫ v).left := by
    change Etale (W.ι ≫ v.left)
    infer_instance
  have hU : B.Contains U.left :=
    size_lt_cutoff_of_isAffine_of_locallyOfFiniteType .fppf B (w ≫ v).left hT
  refine ⟨U, w, inferInstance, hU, inferInstance, inferInstance, ?_⟩
  exact ⟨⟨x, hxW⟩, hx⟩

/-- Every point of an arbitrary standalone family over a bounded base has a
genuine schematic étale presentation with both schemes in the bounded site.
This proves the local size/descent step for the actual family data; it does not
assume a family-classifier equivalence. -/
theorem standaloneFamily_has_bounded_scheme_chart_at
    {T : M9StandaloneDraft.Schemes K} (hT : B.Contains T.left) {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) (t : T.left) :
    ∃ (U Z : M9StandaloneDraft.Schemes K) (v : U ⟶ T) (q : Z ⟶ U)
      (r : yoneda.obj Z ⟶ F.total.obj),
      IsAffine U.left ∧ B.Contains U.left ∧ B.Contains Z.left ∧
        Etale v.left ∧ t ∈ Set.range v.left ∧
        IsPullback r (yoneda.map q) F.projection (yoneda.map v) ∧
        M9StandaloneDraft.SchemeCurve q.left g := by
  obtain ⟨T', Z', v, q, r, hv, ht, hcart, hq⟩ := F.locally_curve t
  letI := hv
  obtain ⟨U, w, hUaff, hU, hw, hwv, htU⟩ :=
    exists_bounded_affine_etale_refinement B K hT v t ht
  let Z := pullback q w
  let p : Z ⟶ U := pullback.snd q w
  let a : Z ⟶ Z' := pullback.fst q w
  have hp : M9StandaloneDraft.SchemeCurve p.left g :=
    schemeCurve_of_isPullback q.left p.left a.left w.left
      ((IsPullback.of_hasPullback q w).map (Over.forget (M9StandaloneDraft.Base K))) hq
  have hZ : B.Contains Z.left := contains_total_of_schemeCurve B K hU p.left hp
  refine ⟨U, Z, w ≫ v, p, yoneda.map a ≫ r,
    hUaff, hU, hZ, hwv, htU, ?_, hp⟩
  have hsmall := (IsPullback.of_hasPullback q w).map yoneda
  simpa only [Functor.map_comp] using hsmall.paste_horiz hcart

end BoundedSchemes

end M9StacksIntegration.AllTestBoundedCharts

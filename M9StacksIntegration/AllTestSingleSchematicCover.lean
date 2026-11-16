module

public import M9StacksIntegration.AllTestBoundedCover
public import M9StacksIntegration.AllTestCurveCoproducts
public import M9StacksIntegration.AllTestBoundedRestriction

/-!
# One actual bounded schematic etale presentation of an original family

The original total sheaf and coefficient field are retained. The chart maps
are glued using its genuine fppf sheaf property; the square is proved
cartesian on the full original test category. The projection of the schematic
total satisfies the literal original all-field-point curve predicate.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestSingleSchematicCover
open AllTestBoundedCover AllTestBoundedCharts AllTestSheafCoproducts
  AllTestCoproductCartesian AllTestCurveCoproducts
universe u

/-- Every original algebraic-space family over a bounded base has one actual
bounded schematic etale cover, with its entire original cartesian square and
its entire original genus predicate. No classifier/full-faithfulness premise
or global schematicity of the original total space is assumed. -/
theorem exists_bounded_schematic_etale_cover
    (B : BigFppfSite.{u}) (K : Type u) [Field K]
    {T : M9StandaloneDraft.Schemes K} (hT : B.Contains T.left) {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) :
    ∃ (U Z : M9StandaloneDraft.Schemes K) (v : U ⟶ T) (q : Z ⟶ U)
      (r : yoneda.obj Z ⟶ F.total.obj),
      B.Contains U.left ∧ B.Contains Z.left ∧ Etale v.left ∧ Surjective v.left ∧
        IsPullback r (yoneda.map q) F.projection (yoneda.map v) ∧
        M9StandaloneDraft.SchemeCurve q.left g := by
  classical
  obtain ⟨W, hWet, hsize, hchart⟩ := standaloneFamily_has_bounded_cover B K hT F
  choose Z q r hW hZ hcart hq using hchart
  let U : W.ι → M9StandaloneDraft.Schemes K := fun j => Over.mk (W.f j ≫ T.hom)
  let v : ∀ j, U j ⟶ T := fun j => Over.homMk (W.f j) rfl
  let Us := sumObject K U
  let Zs := sumObject K Z
  let vs := sumMap K U v
  let qs := sumArrow K Z U q
  let rs := glueMaps K Z F.total r
  have hv := bounded_cover_coproduct B hT W hWet hsize
  change B.Contains Us.left ∧ Etale vs.left ∧ Surjective vs.left at hv
  have hqs : M9StandaloneDraft.SchemeCurve qs.left g := schemeCurve_sumArrow K Z U q g hq
  have hZs : B.Contains Zs.left := contains_total_of_schemeCurve B K hv.1 qs.left hqs
  refine ⟨Us, Zs, vs, qs, rs, hv.1, hZs, hv.2.1, hv.2.2, ?_, hqs⟩
  exact isPullback_glueMaps K Z U F.total F.projection q v r hcart

/-- Every original test base, of arbitrary size in the working universe,
admits a genuine site containing the field and the base, together with the
single bounded schematic etale presentation of the original family. -/
theorem exists_site_and_bounded_schematic_etale_cover
    (K : Type u) [Field K] {T : M9StandaloneDraft.Schemes K} {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) :
    ∃ (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))) (hT : B.Contains T.left)
      (U Z : M9StandaloneDraft.Schemes K) (v : U ⟶ T) (q : Z ⟶ U)
      (r : yoneda.obj Z ⟶ F.total.obj),
      B.Contains U.left ∧ B.Contains Z.left ∧ Etale v.left ∧ Surjective v.left ∧
        IsPullback r (yoneda.map q) F.projection (yoneda.map v) ∧
        M9StandaloneDraft.SchemeCurve q.left g := by
  obtain ⟨B, hK, hT⟩ := AllTestBoundedRestriction.exists_site_contains_test K T
  obtain ⟨U, Z, v, q, r, hU, hZ, hv, hs, hcart, hq⟩ :=
    exists_bounded_schematic_etale_cover B K hT F
  exact ⟨B, hK, hT, U, Z, v, q, r, hU, hZ, hv, hs, hcart, hq⟩

/-- A single schematic etale presentation exists for EVERY original family
on EVERY original test scheme; no fixed-site size restriction remains. -/
theorem exists_schematic_etale_cover
    (K : Type u) [Field K] {T : M9StandaloneDraft.Schemes K} {g : ℕ}
    (F : M9StandaloneDraft.Family K T g) :
    ∃ (U Z : M9StandaloneDraft.Schemes K) (v : U ⟶ T) (q : Z ⟶ U)
      (r : yoneda.obj Z ⟶ F.total.obj),
      Etale v.left ∧ Surjective v.left ∧
        IsPullback r (yoneda.map q) F.projection (yoneda.map v) ∧
        M9StandaloneDraft.SchemeCurve q.left g := by
  obtain ⟨B, hK, hT, U, Z, v, q, r, hU, hZ, hv, hs, hcart, hq⟩ :=
    exists_site_and_bounded_schematic_etale_cover K F
  exact ⟨U, Z, v, q, r, hv, hs, hcart, hq⟩

end M9StacksIntegration.AllTestSingleSchematicCover

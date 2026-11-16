module

public import M9StacksIntegration.AllTestSingleSchematicCover
public import M9StacksIntegration.NativeSchematicCurveFamily

/-!
# Actual native schematic charts of the original all-test families

The coefficient field and all maps over it are retained in the chart data.
The native family is constructed from the same underlying proper smooth
relative curve, using the terminal integer base only for its native ambient
site. Its field fibres are actual pullbacks and have the original H1 genus.
No coarse classifier, family equivalence, or H0 base-change condition is an
assumption or conclusion of this leaf.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeSchematicCharts
open StandaloneCurveCohomology NativeSchematicCurveFamily
universe u

/-- The all-field-point condition recovers the genus over the original field
itself, with the original structural scalar action. -/
theorem genus_eq_of_schemeCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {g : ℕ} (hq : M9StandaloneDraft.SchemeCurve f g) :
    genus f = g := by
  let : IsProper f := hq.1
  have hcart : IsPullback (pullback.fst f (𝟙 _)) (pullback.snd f (𝟙 _)) f
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_hasPullback f (𝟙 _)
  exact (genus_baseChange k k _ _ f hcart).symm.trans (hq.2.2.2 k (𝟙 _)).2

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every native field fibre of the constructed family has an actual
schematic pullback presentation and the original cohomological genus.
This is the literal quantified assertion in `HasFieldPointFibreGenus`, with
no unbuilt genus-stack provider imported. -/
theorem schemeCurveFamily_field_fibre_genus
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    ∀ p : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (schemeCurveFamily B hZ q g hq).base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (r : yoneda.obj V ⟶ (schemeCurveFamily B hZ q g hq).total.obj),
        IsPullback r (yoneda.map v) (schemeCurveFamily B hZ q g hq).toBase.hom
          (yonedaEquiv.symm p.value) ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g := by
  intro p
  let a : p.siteObject ⟶ T := p.value
  refine ⟨pullback q a, pullback.snd q a, yoneda.map (pullback.fst q a), ?_, ?_⟩
  · change IsPullback _ _ (yoneda.map q) (yonedaEquiv.symm p.value)
    have he : yonedaEquiv.symm p.value = yoneda.map a := by
      apply yonedaEquiv.injective
      simp only [Equiv.apply_symm_apply]
      rfl
    convert (IsPullback.of_hasPullback q a).map yoneda using 1 <;>
      first | rfl | exact he | exact he.symm
  · apply genus_eq_of_schemeCurve
    exact schemeCurve_of_isPullback _ _ _ _
      ((IsPullback.of_hasPullback q a).map (BigFppfOver.toScheme B integerBase hZ)) hq

/-- Put an original bounded test scheme in the native integer-base site.
The original scheme itself is retained literally. -/
abbrev integerObject {K : Type u} [Field K] (T : M9StandaloneDraft.Schemes K)
    (hT : B.Contains T.left) : BigFppfOver B integerBase hZ :=
  siteObject B integerBase hZ hT (specULiftZIsTerminal.from T.left)

/-- The actual original scheme map, regarded in the native integer-base site. -/
def integerMap {K : Type u} [Field K] {Z T : M9StandaloneDraft.Schemes K}
    (hZs : B.Contains Z.left) (hT : B.Contains T.left) (q : Z ⟶ T) :
    integerObject B hZ Z hZs ⟶ integerObject B hZ T hT :=
  Over.homMk (ObjectProperty.homMk q.left)
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

@[simp] theorem integerMap_toScheme {K : Type u} [Field K]
    {Z T : M9StandaloneDraft.Schemes K}
    (hZs : B.Contains Z.left) (hT : B.Contains T.left) (q : Z ⟶ T) :
    (BigFppfOver.toScheme B integerBase hZ).map (integerMap B hZ hZs hT q) = q.left := rfl

/-- The original K-structure, remembered as an actual map in the native site. -/
def coefficientMap {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (T : M9StandaloneDraft.Schemes K) (hT : B.Contains T.left) :
    integerObject B hZ T hT ⟶
      integerObject B hZ (Over.mk (𝟙 (Spec (.of K)))) hK :=
  Over.homMk (ObjectProperty.homMk T.hom)
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The native chart projection preserves the original coefficient structure. -/
theorem integerMap_coefficientMap {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) {Z T : M9StandaloneDraft.Schemes K}
    (hZs : B.Contains Z.left) (hT : B.Contains T.left) (q : Z ⟶ T) :
    integerMap B hZ hZs hT q ≫ coefficientMap B hZ hK T hT =
      coefficientMap B hZ hK Z hZs := by
  apply (BigFppfOver.toScheme B integerBase hZ).map_injective
  change q.left ≫ T.hom = Z.hom
  exact Over.w q

/-- Every original test and its original field admit a native site also
containing the terminal integer base. No bound on the test is assumed. -/
theorem exists_site_contains_original_test (K : Type u) [Field K]
    (T : M9StandaloneDraft.Schemes K) :
    ∃ B : BigFppfSite.{u}, B.Contains integerBase ∧
      B.Contains (Spec (.of K)) ∧ B.Contains T.left := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({integerBase, Spec (.of K), T.left} : Set Scheme.{u})
  exact ⟨B, hB _ (by simp), hB _ (by simp), hB _ (by simp)⟩

end M9StacksIntegration.AllTestNativeSchematicCharts

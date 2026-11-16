module

public import M9StacksIntegration.StandaloneModuliDraft
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Literal scheme families on the full original all-test site

These actual Yoneda constructions and their inverse-map proofs are isolated
from the staged CoarseSiteComparison source, so their proof does not depend
on the unbuilt native moduli stack. The unchanged all-test definitions are
imported literally. This proves the schematic comparison only; a general
algebraic-space family is not assumed to have a schematic total space.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestSchemeFamilies
universe u

section StandaloneSchemeFamilies

variable (K : Type u) [Field K]

/-- The actual representable algebraic space on the full all-test site. -/
def standaloneSchemeSpace (Z : M9StandaloneDraft.Schemes K) : M9StandaloneDraft.Space K where
  obj := yoneda.obj Z
  isSheaf := (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  diagonal := by
    refine Functor.relativelyRepresentable.diag_of_map_from_obj fun T a => ?_
    obtain ⟨a, rfl⟩ := yoneda.map_surjective a
    exact Functor.relativelyRepresentable.map yoneda a
  atlas := by
    refine ⟨Z, 𝟙 _, ?_, ?_⟩
    · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
      intro U V a b f h
      letI : IsIso (yoneda.map f) := h.isIso_snd_of_isIso
      letI : IsIso f := Yoneda.fullyFaithful.isIso_of_isIso_map f
      change Etale f.left
      infer_instance
    · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
      intro U V a b f h
      letI : IsIso (yoneda.map f) := h.isIso_snd_of_isIso
      letI : IsIso f := Yoneda.fullyFaithful.isIso_of_isIso_map f
      change Surjective f.left
      infer_instance

/-- A genuine scheme curve family gives an actual standalone family on the
entire test base. No field-point or finite-type restriction is imposed on it. -/
def standaloneSchemeFamily {T Z : M9StandaloneDraft.Schemes K} (q : Z ⟶ T)
    (g : ℕ) (hq : M9StandaloneDraft.SchemeCurve q.left g) : M9StandaloneDraft.Family K T g where
  total := standaloneSchemeSpace K Z
  projection := yoneda.map q
  locally_curve := by
    intro t
    refine ⟨T, Z, 𝟙 _, q, 𝟙 _, inferInstance, ⟨t, rfl⟩, ?_, hq⟩
    change IsPullback (𝟙 _) (yoneda.map q) (yoneda.map q) (yoneda.map (𝟙 T))
    rw [CategoryTheory.Functor.map_id]
    exact IsPullback.id_horiz (yoneda.map q)

/-- Isomorphisms of the actual all-test representable families are exactly
isomorphisms of their original schemes over the entire base. -/
theorem standaloneSchemeFamily_isomorphic_iff
    {T Z Z' : M9StandaloneDraft.Schemes K} (q : Z ⟶ T) (q' : Z' ⟶ T)
    (g : ℕ) (hq : M9StandaloneDraft.SchemeCurve q.left g)
    (hq' : M9StandaloneDraft.SchemeCurve q'.left g) :
    M9StandaloneDraft.FamilyIsomorphic K
        (standaloneSchemeFamily K q g hq) (standaloneSchemeFamily K q' g hq') ↔
      ∃ e : Z ≅ Z', e.hom ≫ q' = q := by
  change (∃ e : yoneda.obj Z ≅ yoneda.obj Z', e.hom ≫ yoneda.map q' = yoneda.map q) ↔ _
  constructor
  · rintro ⟨e, he⟩
    let e' : Z ≅ Z' := Yoneda.fullyFaithful.preimageIso e
    refine ⟨e', ?_⟩
    apply yoneda.map_injective
    rw [Functor.map_comp]
    change yoneda.map (Yoneda.fullyFaithful.preimage e.hom) ≫ yoneda.map q' = yoneda.map q
    rw [Yoneda.fullyFaithful.map_preimage]
    exact he
  · rintro ⟨e, he⟩
    refine ⟨yoneda.mapIso e, ?_⟩
    change yoneda.map e.hom ≫ yoneda.map q' = yoneda.map q
    rw [← Functor.map_comp, he]

/-- A cartesian morphism between actual representable all-test families comes
from exactly one original scheme morphism, with the cartesian square reflected
by Yoneda. This is full faithfulness for schematic family maps. -/
theorem existsUnique_scheme_map_of_cartesian
    {T U Z Z' : M9StandaloneDraft.Schemes K} (q : Z ⟶ T) (q' : Z' ⟶ U)
    (a : U ⟶ T) (r : yoneda.obj Z' ⟶ yoneda.obj Z)
    (hr : IsPullback r (yoneda.map q') (yoneda.map q) (yoneda.map a)) :
    ∃! b : Z' ⟶ Z, yoneda.map b = r ∧ IsPullback b q' q a := by
  let b := yoneda.preimage r
  have hb : yoneda.map b = r := yoneda.map_preimage r
  refine ⟨b, ⟨hb, ?_⟩, ?_⟩
  · rw [← hb] at hr
    exact hr.of_map_of_faithful yoneda
  · intro b' hb'
    exact yoneda.map_injective (hb'.1.trans hb.symm)

end StandaloneSchemeFamilies

end M9StacksIntegration.AllTestSchemeFamilies

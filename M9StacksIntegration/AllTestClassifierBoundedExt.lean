module

public import M9StacksIntegration.AllTestSpecToAffineFamilyValues
public import M9StacksIntegration.AllTestRelativeFamilyModel

/-!
# Determination of full original classifiers by spectra and bounded tests

Agreement on every literal spectrum over the original field determines a
classifier on all original families, using the genuine affine adapter and
uniqueness of the full sheaf extension. Spectra of zero algebras are included.

Agreement on every original family over the bounded site already suffices:
each original affine family has an actual finite-stage family in that site,
and the classifiers' own naturality transports its common value. No size
bound on the original algebra or supplied finite-stage model is required.
-/

set_option autoImplicit false
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace M9StacksIntegration.AllTestClassifierBoundedExt
open AllTestBoundedCharts AllTestSpecToAffineFamilyValues
  AllTestAffineClassifierExtension AllTestRelativeFamilyModel

universe u
variable (K : Type u) [Field K]

/-- Equality on all literal spectra, including zero algebras, determines the
actual classifier on all original bases and all original families. -/
theorem classifier_ext_of_spec (g : ℕ)
    {M : M9StandaloneDraft.Presheaves K}
    (hM : Presheaf.IsSheaf
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (c d : M9StandaloneDraft.Classifier K g M)
    (hSpec : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (F : M9StandaloneDraft.Family K (specOverK K A) g),
      c.value (specOverK K A) F = d.value (specOverK K A) F) : c = d := by
  let s : SpecFamilyValues K g M :=
    { value := fun A _ _ F => c.value (specOverK K A) F
      naturality := by
        intro A R _ _ _ _ φ F G r hr
        exact c.naturality _ _ _ F G r hr }
  have hc : c = extend K (toAffineFamilyValues K s) hM := by
    apply extend_unique K (toAffineFamilyValues K s) hM c
    intro T hT F
    exact (toAffine_agreesClassifier K s c (by intros; rfl) T hT F).symm
  have hd : d = extend K (toAffineFamilyValues K s) hM := by
    apply extend_unique K (toAffineFamilyValues K s) hM d
    intro T hT F
    exact (toAffine_agreesClassifier K s d
      (by intro A _ _ G; exact hSpec A G) T hT F).symm
  exact hc.trans hd.symm

/-- Equality on all original families over one field-containing bounded site
determines the full original classifier, without a bound on the other tests. -/
theorem classifier_ext_of_bounded (B : BigFppfSite.{u})
    (hK : B.Contains (Spec (.of K))) (g : ℕ)
    {M : M9StandaloneDraft.Presheaves K}
    (hM : Presheaf.IsSheaf
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (c d : M9StandaloneDraft.Classifier K g M)
    (hB : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
      (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
      c.value ((boundedInclusion B K hK).obj T) F =
        d.value ((boundedInclusion B K hK).obj T) F) : c = d := by
  apply classifier_ext_of_spec K g hM c d
  intro A _ _ F
  obtain ⟨i, Fi, r, hi, hr⟩ :=
    exists_original_family_model_in_field_site K A B hK g F
  let T : BigFppfOver B (Spec (.of K)) hK :=
    siteObject B (Spec (.of K)) hK hi ((AdjoinFinset.specToBase K A).app i)
  let a : specOverK K A ⟶ (boundedInclusion B K hK).obj T :=
    Over.homMk ((AdjoinFinset.specCone K A).π.app i)
      (AdjoinFinset.specCone_π_comp K A i)
  calc
    c.value (specOverK K A) F =
        M.map a.op (c.value ((boundedInclusion B K hK).obj T) Fi) :=
      (c.naturality _ _ a Fi F r hr).symm
    _ = M.map a.op (d.value ((boundedInclusion B K hK).obj T) Fi) :=
      congrArg (M.map a.op) (hB T Fi)
    _ = d.value (specOverK K A) F := d.naturality _ _ a Fi F r hr

end M9StacksIntegration.AllTestClassifierBoundedExt

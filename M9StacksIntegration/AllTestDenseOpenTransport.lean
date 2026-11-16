module

public import M9StacksIntegration.StandaloneDenseOpen

/-!
# Isomorphism transport of the literal all-original-test dense-open property

The represented test schemes and their maps are unchanged by this transport.
In particular the density conclusion is retained on every original etale chart,
rather than replaced by a statement about points or bounded tests.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.AllTestDenseOpenTransport

variable (K : Type u) [Field K]

/-- The actual represented open-immersion property is invariant under an
isomorphism of the source and target arrow. -/
theorem openImmersion_iff_of_iso
    {F G F' G' : M9StandaloneDraft.Presheaves K}
    (j : F ⟶ G) (j' : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G')
    (h : j ≫ eG.hom = eF.hom ≫ j') :
    M9StandaloneDraft.OpenImmersion K j ↔ M9StandaloneDraft.OpenImmersion K j' :=
  (MorphismProperty.inverseImage (@IsOpenImmersion.{u})
    (Over.forget (M9StandaloneDraft.Base K))).presheaf.arrow_mk_iso_iff
      (Arrow.isoMk eF eG h.symm)

/-- The etale property on all represented original pullbacks is invariant
under an actual isomorphism of arrows. -/
theorem etale_iff_of_iso
    {F G F' G' : M9StandaloneDraft.Presheaves K}
    (j : F ⟶ G) (j' : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G')
    (h : j ≫ eG.hom = eF.hom ≫ j') :
    (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf j ↔
    (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf j' :=
  (MorphismProperty.inverseImage (@Etale.{u})
    (Over.forget (M9StandaloneDraft.Base K))).presheaf.arrow_mk_iso_iff
      (Arrow.isoMk eF eG h.symm)

/-- Actual isomorphisms transport density while preserving the same
original etale test, the same represented pullback, and its actual scheme map. -/
theorem denseOpen_of_iso
    {F G F' G' : M9StandaloneDraft.Presheaves K}
    (j : F ⟶ G) (j' : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G')
    (h : j ≫ eG.hom = eF.hom ≫ j')
    (hj : M9StandaloneDraft.DenseOpen K j) :
    M9StandaloneDraft.DenseOpen K j' := by
  refine ⟨(openImmersion_iff_of_iso K j j' eF eG h).mp hj.1, ?_⟩
  intro V v hv P a b hp
  have hback : j' ≫ eG.inv = eF.inv ≫ j := by
    apply (cancel_epi eF.hom).mp
    simpa [Category.assoc] using congrArg (fun m => m ≫ eG.inv) h.symm
  have hv' : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf (v ≫ eG.inv) :=
    (etale_iff_of_iso K v (v ≫ eG.inv) (Iso.refl _) eG.symm (by simp)).mp hv
  have hp' : IsPullback (b ≫ eF.inv) (yoneda.map a) j (v ≫ eG.inv) := by
    apply hp.of_iso (Iso.refl _) eF.symm (Iso.refl _) eG.symm
    · simp
    · simp
    · exact hback
    · simp
  exact hj.2 V (v ≫ eG.inv) hv' P a (b ≫ eF.inv) hp'

/-- Literal all-test dense openness is unchanged by actual source/target
isomorphisms; no density or representability premise is added. -/
theorem denseOpen_iff_of_iso
    {F G F' G' : M9StandaloneDraft.Presheaves K}
    (j : F ⟶ G) (j' : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G')
    (h : j ≫ eG.hom = eF.hom ≫ j') :
    M9StandaloneDraft.DenseOpen K j ↔ M9StandaloneDraft.DenseOpen K j' := by
  refine ⟨denseOpen_of_iso K j j' eF eG h, ?_⟩
  apply denseOpen_of_iso K j' j eF.symm eG.symm
  apply (cancel_epi eF.hom).mp
  simpa [Category.assoc] using congrArg (fun m => m ≫ eG.inv) h.symm

end M9StacksIntegration.AllTestDenseOpenTransport

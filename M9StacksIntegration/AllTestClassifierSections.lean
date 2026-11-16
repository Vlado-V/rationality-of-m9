module

public import M9StacksIntegration.AllTestOriginalFamilyCategory

/-!
# Literal ORIGINAL classifiers as actual natural sections

A Standalone Classifier on ALL original families is exactly a natural
section of the target presheaf pulled back to the ACTUAL original-family
category. Its literal algebraic-space categorical universality is exactly
the corresponding universal factorization of these actual sections.
No original/native classifier comparison or coarse-existence premise is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestClassifierSections
open AllTestOriginalFamilyCategory
universe u
variable (K : Type u) [Field K] (g : ℕ)

/-- The actual terminal presheaf on the actual ORIGINAL family category. -/
abbrev terminalSectionSource : (CurveObject K g)ᵒᵖ ⥤ Type u :=
  (Functor.const (CurveObject K g)ᵒᵖ).obj PUnit.{u+1}

/-- Actual natural sections on all ORIGINAL families and Cartesian arrows. -/
abbrev Sections (M : M9StandaloneDraft.Presheaves K) :=
  terminalSectionSource K g ⟶ (projection K g).op ⋙ M

/-- Literal classifiers are determined by values on their actual original families. -/
theorem classifier_ext {M : M9StandaloneDraft.Presheaves K}
    (c d : M9StandaloneDraft.Classifier K g M)
    (h : ∀ (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g),
      c.value T F = d.value T F) : c = d := by
  cases c with
  | mk cv cn =>
    cases d with
    | mk dv dn =>
      have hv : cv = dv := funext fun T => funext fun F => h T F
      cases hv
      rfl

/-- A literal classifier gives its ACTUAL section on the original family category. -/
def classifierSection {M : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M) : Sections K g M where
  app X := TypeCat.ofHom fun _ => c.value X.unop.base X.unop.family
  naturality := by
    intro X Y f
    ext x
    exact (c.naturality X.unop.base Y.unop.base f.unop.baseMap
      X.unop.family Y.unop.family f.unop.totalMap f.unop.cartesian).symm

/-- An actual natural section constructs a literal ALL-original-test classifier. -/
def sectionClassifier {M : M9StandaloneDraft.Presheaves K}
    (s : Sections K g M) : M9StandaloneDraft.Classifier K g M where
  value T F := s.app (op (⟨T, F⟩ : CurveObject K g)) PUnit.unit
  naturality := by
    intro T U a F G r hcart
    let f : (⟨U, G⟩ : CurveObject K g) ⟶ ⟨T, F⟩ := ⟨a, r, hcart⟩
    have h := ConcreteCategory.congr_hom (s.naturality f.op) PUnit.unit
    exact h.symm

/-- A genuine equivalence of the literal classifier data and actual sections,
with inverse laws proved on the original objects and field maps. -/
def classifierEquivSections (M : M9StandaloneDraft.Presheaves K) :
    M9StandaloneDraft.Classifier K g M ≃ Sections K g M where
  toFun := classifierSection K g
  invFun := sectionClassifier K g
  left_inv c := classifier_ext K g _ _ (fun _ _ => rfl)
  right_inv s := by
    ext X x
    cases x
    rfl

/-- Postcomposition of actual classifier sections uses the SAME target map
on every original test and original family. -/
theorem section_comp_iff
    {M N : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M) (d : M9StandaloneDraft.Classifier K g N)
    (f : M ⟶ N) :
    classifierSection K g c ≫ Functor.whiskerLeft (projection K g).op f =
        classifierSection K g d ↔
      ∀ (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g),
        f.app (op T) (c.value T F) = d.value T F := by
  constructor
  · intro h T F
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op (⟨T, F⟩ : CurveObject K g))) PUnit.unit
  · intro h
    ext X x
    exact h X.unop.base X.unop.family

/-- The literal FULL all-algebraic-space categorical universal property is
EXACTLY universal factorization of actual natural sections on the actual
original-family category. No universality or classifier comparison is assumed. -/
theorem isCategorical_iff_sections
    {M : M9StandaloneDraft.Presheaves K} (c : M9StandaloneDraft.Classifier K g M) :
    M9StandaloneDraft.IsCategorical K c ↔
      ∀ (W : M9StandaloneDraft.Space K) (s : Sections K g W.obj),
        ∃! f : M ⟶ W.obj,
          classifierSection K g c ≫ Functor.whiskerLeft (projection K g).op f = s := by
  constructor
  · intro h W s
    obtain ⟨f, hf, hu⟩ := h W (sectionClassifier K g s)
    have hsection : classifierSection K g (sectionClassifier K g s) = s :=
      (classifierEquivSections K g W.obj).right_inv s
    refine ⟨f, ?_, ?_⟩
    · rw [← hsection]
      exact (section_comp_iff K g c (sectionClassifier K g s) f).mpr hf
    · intro f' hf'
      apply hu f'
      apply (section_comp_iff K g c (sectionClassifier K g s) f').mp
      exact hf'.trans hsection.symm
  · intro h W d
    obtain ⟨f, hf, hu⟩ := h W (classifierSection K g d)
    refine ⟨f, (section_comp_iff K g c d f).mp hf, ?_⟩
    intro f' hf'
    exact hu f' ((section_comp_iff K g c d f').mpr hf')

end M9StacksIntegration.AllTestClassifierSections

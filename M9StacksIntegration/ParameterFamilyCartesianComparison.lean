module

public import M9StacksIntegration.ParameterFamilyDeformation
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCover

/-!
# Actual Cartesian comparison for pointed family deformations

The canonical pullback of a flat family along a parameter morphism is
compared with the original family on every pointed Artinian test. Both
the total-space isomorphism and the special-fibre marking come from the
original pullback squares. No deformation-class or tangent-map identity
is supplied as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Examples

universe u

namespace M9Native.ParameterFamilyCartesianComparison

variable {X T P : Scheme.{u}} (p : X ⟶ T) (f : P ⟶ T)

/-- The actual family after the specified parameter change. -/
abbrev changedFamily : pullback p f ⟶ P := pullback.snd p f

/-- Pasting the two original pullback squares identifies every changed
test fibre with the original family's fibre at the composite test. -/
def testIso {A : Scheme.{u}} (a : A ⟶ P) :
    pullback (changedFamily p f) a ≅ pullback p (a ≫ f) :=
  ((IsPullback.of_hasPullback (changedFamily p f) a).paste_horiz
    (IsPullback.of_hasPullback p f)).isoPullback

@[reassoc] theorem testIso_hom_fst {A : Scheme.{u}} (a : A ⟶ P) :
    (testIso p f a).hom ≫ pullback.fst p (a ≫ f) =
      pullback.fst (changedFamily p f) a ≫ pullback.fst p f :=
  IsPullback.isoPullback_hom_fst _

@[reassoc] theorem testIso_hom_snd {A : Scheme.{u}} (a : A ⟶ P) :
    (testIso p f a).hom ≫ pullback.snd p (a ≫ f) =
      pullback.snd (changedFamily p f) a :=
  IsPullback.isoPullback_hom_snd _

@[reassoc] theorem testIso_inv_snd {A : Scheme.{u}} (a : A ⟶ P) :
    (testIso p f a).inv ≫ pullback.snd (changedFamily p f) a =
      pullback.snd p (a ≫ f) :=
  IsPullback.isoPullback_inv_snd _

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  [Flat p] (i : Spec (.of k) ⟶ P)

/-- The actual special-fibre comparison, over the original coefficient field. -/
def fibreIso :
    (ParameterFamilyDeformation.fibre (changedFamily p f) i).left ≅
      (ParameterFamilyDeformation.fibre p (i ≫ f)).left :=
  testIso p f i

omit [Flat p] in
/-- The special-fibre isomorphism retains the actual structure map. -/
theorem fibreIso_over :
    (fibreIso p f i).hom ≫ (ParameterFamilyDeformation.fibre p (i ≫ f)).hom =
      (ParameterFamilyDeformation.fibre (changedFamily p f) i).hom :=
  testIso_hom_snd p f i

variable (A : ArtinianLocalAlgCat.{u,u,u} Λ k)
  (a : baseSpec A ⟶ P) (ha : residueSpecMap A ≫ a = i)

include ha in
/-- Composing the actual pointed test retains its original residue marking. -/
theorem composite_residue : residueSpecMap A ≫ (a ≫ f) = i ≫ f := by
  rw [← Category.assoc, ha]

/-- The original family on the composite test, with its marking transported
along the genuine special-fibre isomorphism. Its total space stays the
original family's pullback. -/
def compositeDeformation :
    SchemeDeformationCategory (Λ := Λ) (k := k)
      (ParameterFamilyDeformation.fibre (changedFamily p f) i) :=
  transportDeformation (fibreIso p f i).hom (fibreIso_over p f i)
    (ParameterFamilyDeformation.deformation p (i ≫ f) A (a ≫ f)
      (composite_residue f i A a ha))

/-- Transport changes only the special-fibre marking, never the original
total family or Artinian coefficient algebra. -/
theorem compositeDeformation_scheme :
    (compositeDeformation p f i A a ha).scheme = pullback p (a ≫ f) := rfl

theorem compositeDeformation_base :
    (compositeDeformation p f i A a ha).base = A := rfl

/-- The actual pullback-pasting isomorphism also commutes with the original
special-fibre maps, before passing to any deformation class. -/
theorem specialMap_testIso :
    (ParameterFamilyDeformation.deformation (changedFamily p f) i A a ha).specialMap ≫
      (testIso p f a).hom =
        (compositeDeformation p f i A a ha).specialMap := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testIso_hom_fst,
      ParameterFamilyDeformation.deformation, pullback.lift_fst_assoc,
      compositeDeformation, transportDeformation, fibreIso,
      pullback.lift_fst, testIso_hom_fst]
  · simp only [Category.assoc, testIso_hom_snd,
      ParameterFamilyDeformation.deformation, pullback.lift_snd,
      compositeDeformation, transportDeformation, fibreIso,
      testIso_hom_snd_assoc]

/-- A genuine native deformation arrow over the identity of the SAME
Artinian algebra. Its total map is the original pullback-pasting iso. -/
def comparisonHom :
    compositeDeformation p f i A a ha ⟶
      ParameterFamilyDeformation.deformation (changedFamily p f) i A a ha where
  base := 𝟙 A
  map := (testIso p f a).hom
  cartesian := by
    rw [baseSpecMap_id]
    change IsPullback (testIso p f a).hom
      (pullback.snd (changedFamily p f) a) (pullback.snd p (a ≫ f))
      (𝟙 (baseSpec A))
    exact IsPullback.of_horiz_isIso ⟨by
      rw [testIso_hom_snd, Category.comp_id]⟩
  special_compat := specialMap_testIso p f i A a ha

/-- The inverse comparison is also over the original identity coefficient map. -/
def comparisonInv :
    ParameterFamilyDeformation.deformation (changedFamily p f) i A a ha ⟶
      compositeDeformation p f i A a ha where
  base := 𝟙 A
  map := (testIso p f a).inv
  cartesian := by
    rw [baseSpecMap_id]
    change IsPullback (testIso p f a).inv
      (pullback.snd p (a ≫ f)) (pullback.snd (changedFamily p f) a)
      (𝟙 (baseSpec A))
    exact IsPullback.of_horiz_isIso ⟨by
      rw [testIso_inv_snd, Category.comp_id]⟩
  special_compat := by
    rw [← specialMap_testIso p f i A a ha, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/-- The two actual marked deformations are isomorphic, not merely assigned
the same abstract class. -/
def comparisonIso :
    compositeDeformation p f i A a ha ≅
      ParameterFamilyDeformation.deformation (changedFamily p f) i A a ha where
  hom := comparisonHom p f i A a ha
  inv := comparisonInv p f i A a ha
  hom_inv_id := by
    apply SchemeDeformationCategory.Hom.ext
    · change (𝟙 A) ≫ (𝟙 A) = 𝟙 A
      exact Category.id_comp _
    · exact (testIso p f a).inv_hom_id
  inv_hom_id := by
    apply SchemeDeformationCategory.Hom.ext
    · change (𝟙 A) ≫ (𝟙 A) = 𝟙 A
      exact Category.id_comp _
    · exact (testIso p f a).hom_inv_id

end M9Native.ParameterFamilyCartesianComparison

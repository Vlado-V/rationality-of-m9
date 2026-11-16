module

public import M9StacksIntegration.GenusNineOriginalFamilyFunctor
public import M9StacksIntegration.OriginalClassifierNativeCompatibility

/-!
A full original classifier restricts to the actual chosen smooth-genus
source, over every native base. The original-family functor and its base
square are derived actual producers. The named native value recovers the
literal original classifier value by the actual target recovery unit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.GenusNineOriginalClassifierNativeRestriction

open M9StacksIntegration M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestBoundedOriginalRecovery

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)
  (W : AlgebraicSpaces B (Spec (.of K)) hK)
  (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj W))

/-- The literal original classifier value on the derived original family. -/
def originalValue (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    ((originalPresheafFunctor K B hK).obj W).obj
      (op ((boundedInclusion B K hK).obj
        ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))) :=
  d.value ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base
    ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family

/-- A named native value derived from the full original classifier. -/
def nativeValue (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    W.obj.obj (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)) :=
  OriginalClassifierNativeRestriction.nativeValue K B hK g
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) W d x

/-- The actual target recovery unit sends the literal original value to the native value. -/
theorem nativeValue_eq
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    nativeValue B hZ K hK g hg W d x =
      (originalNativeRestrictionSmallIso K B hK W.obj W.property).hom.app
        (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
        (originalValue B hZ K hK g hg W d x) := rfl

/-- Every actual source object recovers its same literal original classifier value. -/
theorem originalValue_recovery
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (originalNativeRestrictionSmallIso K B hK W.obj W.property).inv.app
        (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
        (nativeValue B hZ K hK g hg W d x) =
      d.value ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base
        ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family := by
  rw [nativeValue_eq]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (originalNativeRestrictionSmallIso K B hK W.obj W.property).hom_inv_id
    (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)))
    (originalValue B hZ K hK g hg W d x)

/-- Native naturality holds for every actual source arrow over every native base. -/
theorem nativeValue_naturality
    {x y : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj}
    (a : x ⟶ y) :
    W.obj.map ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).map a).op
        (nativeValue B hZ K hK g hg W d y) =
      nativeValue B hZ K hK g hg W d x :=
  OriginalClassifierNativeRestriction.nativeValue_naturality K B hK g
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) W d a

/-- Actual native target maps commute with the restriction of full original classifiers. -/
theorem nativeValue_postcompose
    (V : AlgebraicSpaces B (Spec (.of K)) hK) (f : W ⟶ V)
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    nativeValue B hZ K hK g hg V
        (OriginalClassifierNativeCompatibility.postcompose K g d
          ((originalPresheafFunctor K B hK).map f)) x =
      f.hom.app (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
        (nativeValue B hZ K hK g hg W d x) :=
  OriginalClassifierNativeCompatibility.nativeValue_postcompose K g B hK
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) d f x

/-- Native equality is exactly literal original-value equality on the same actual family. -/
theorem nativeValue_eq_iff
    (c : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj W))
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    nativeValue B hZ K hK g hg W c x = nativeValue B hZ K hK g hg W d x ↔
      c.value ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base
          ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family =
        d.value ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base
          ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family :=
  OriginalClassifierNativeCompatibility.nativeValue_eq_iff K g B hK
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) W c d x

/-- Native pointwise factorization is exactly original factorization on all actual families. -/
theorem nativeValue_factorization_iff
    (V : AlgebraicSpaces B (Spec (.of K)) hK)
    (c : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj V))
    (f : V ⟶ W) :
    (∀ x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj,
      f.hom.app (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
        (nativeValue B hZ K hK g hg V c x) = nativeValue B hZ K hK g hg W d x) ↔
    ∀ x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj,
      ((originalPresheafFunctor K B hK).map f).app
          (op ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base)
          (c.value ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base
            ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family) =
        d.value ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base
          ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family := by
  constructor
  · intro h x
    apply (nativeValue_eq_iff B hZ K hK g hg W d
      (OriginalClassifierNativeCompatibility.postcompose K g c
        ((originalPresheafFunctor K B hK).map f)) x).mp
    rw [nativeValue_postcompose]
    exact h x
  · intro h x
    have hx := (nativeValue_eq_iff B hZ K hK g hg W d
      (OriginalClassifierNativeCompatibility.postcompose K g c
        ((originalPresheafFunctor K B hK).map f)) x).mpr (h x)
    rw [nativeValue_postcompose] at hx
    exact hx

/-- The actual chosen-source functor into the actual native algebraic-space category. -/
abbrev targetFunctor :=
  OriginalClassifierNativeRestriction.targetFunctor K B hK g
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) W d

/-- The specified actual native bases are retained literally. -/
theorem targetFunctor_comp :
    targetFunctor B hZ K hK g hg W d ⋙ discreteProjection W.obj =
      (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p :=
  OriginalClassifierNativeRestriction.targetFunctor_comp K B hK g
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) W d

/-- A full original classifier gives the actual native based functor needed by coarse universality. -/
def classifier :
    (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val ⥤ᵇ
      (Stack.fibredCategory B (Spec (.of K)) hK W.obj).val :=
  OriginalClassifierNativeRestriction.classifier K B hK g
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) W d

/-- Its based projection is the actual chosen-source projection. -/
theorem classifier_comp :
    (classifier B hZ K hK g hg W d).toFunctor ⋙ discreteProjection W.obj =
      (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p :=
  (classifier B hZ K hK g hg W d).w

/-- Naming the actual based functor gives exactly the constructed native value. -/
theorem classifier_namedValue
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    sectionOfBasedFunctor (classifier B hZ K hK g hg W d).toFunctor
        (classifier B hZ K hK g hg W d).w x =
      nativeValue B hZ K hK g hg W d x :=
  OriginalClassifierNativeRestriction.classifier_namedValue K B hK g
    (GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg) W d x

/-- The named native classifier recovers the same original value on every actual object. -/
theorem classifier_originalValue_recovery
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (originalNativeRestrictionSmallIso K B hK W.obj W.property).inv.app
        (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
        (sectionOfBasedFunctor (classifier B hZ K hK g hg W d).toFunctor
          (classifier B hZ K hK g hg W d).w x) =
      d.value ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).base
        ((GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x).family := by
  rw [classifier_namedValue]
  exact originalValue_recovery B hZ K hK g hg W d x

/-- The literal genus-nine restriction into the same actual native target. -/
abbrev genusNine_classifier
    (d₉ : M9StandaloneDraft.Classifier K 9 ((originalPresheafFunctor K B hK).obj W)) :=
  classifier B hZ K hK 9 (by decide) W d₉

/-- The literal genus-nine named native value on every actual source object. -/
abbrev genusNine_nativeValue
    (d₉ : M9StandaloneDraft.Classifier K 9 ((originalPresheafFunctor K B hK).obj W)) :=
  nativeValue B hZ K hK 9 (by decide) W d₉

/-- Literal genus-nine recovery keeps the actual constructed original family. -/
theorem genusNine_originalValue_recovery
    (d₉ : M9StandaloneDraft.Classifier K 9 ((originalPresheafFunctor K B hK).obj W))
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK 9 (by decide)).val.val.obj) :
    (originalNativeRestrictionSmallIso K B hK W.obj W.property).inv.app
        (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK 9 (by decide)).obj x))
        (sectionOfBasedFunctor (genusNine_classifier B hZ K hK W d₉).toFunctor
          (genusNine_classifier B hZ K hK W d₉).w x) =
      d₉.value ((GenusNineOriginalFamilyFunctor.genusNineToOriginal B hZ K hK).obj x).base
        ((GenusNineOriginalFamilyFunctor.genusNineToOriginal B hZ K hK).obj x).family :=
  classifier_originalValue_recovery B hZ K hK 9 (by decide) W d₉ x

end M9Native.GenusNineOriginalClassifierNativeRestriction

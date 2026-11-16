module

public import M9StacksIntegration.OriginalClassifierNativeRestriction
public import M9StacksIntegration.AllTestNativeOriginalUnit

/-! Postcomposition and pointwise recovery for the actual restriction of
full original classifiers. Both use the proved natural recovery unit; no
classifier agreement or comparison compatibility is supplied as data. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite

namespace M9StacksIntegration.OriginalClassifierNativeCompatibility
open AllTestOriginalFamilyCategory AllTestClassifierSections AllTestBoundedCharts
  AllTestBoundedRestriction AllTestBoundedOriginalRecovery AllTestNativeOriginalFunctor
  AllTestNativeOriginalUnit OriginalClassifierNativeRestriction

universe u uD
variable (K : Type u) [Field K] (g : ℕ)

/-- Postcompose a full original classifier with an actual presheaf map. -/
def postcompose {M N : M9StandaloneDraft.Presheaves K}
    (d : M9StandaloneDraft.Classifier K g M) (f : M ⟶ N) :
    M9StandaloneDraft.Classifier K g N where
  value T F := f.app (op T) (d.value T F)
  naturality T U a F G r h := by
    rw [← d.naturality T U a F G r h]
    exact ConcreteCategory.congr_hom (f.naturality a.op).symm (d.value T F)

/-- This is actual postcomposition of the original section. -/
theorem classifierSection_postcompose {M N : M9StandaloneDraft.Presheaves K}
    (d : M9StandaloneDraft.Classifier K g M) (f : M ⟶ N) :
    classifierSection K g (postcompose K g d f) =
      classifierSection K g d ≫ Functor.whiskerLeft (projection K g).op f := rfl

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  {D : Type uD} [Category.{u} D]
  (p : D ⥤ BigFppfOver B (Spec (.of K)) hK)
  (Φ : D ⥤ CurveObject K g)
  (hΦ : Φ ⋙ projection K g = p ⋙ boundedInclusion B K hK)

/-- The actual source-base transport followed by the natural recovery unit. -/
def recoveryIso (M : AlgebraicSpaces B (Spec (.of K)) hK) :
    Φ.op ⋙ (projection K g).op ⋙ (originalPresheafFunctor K B hK).obj M ≅
      p.op ⋙ M.obj :=
  eqToIso (by
    change (Φ ⋙ projection K g).op ⋙ (originalPresheafFunctor K B hK).obj M =
      (p ⋙ boundedInclusion B K hK).op ⋙ (originalPresheafFunctor K B hK).obj M
    rw [hΦ]) ≪≫
    Functor.isoWhiskerLeft p.op (originalNativeRestrictionSmallIso K B hK M.obj M.property)

/-- The restricted section uses exactly this proved recovery, on every object. -/
theorem nativeSection_recovery (M : AlgebraicSpaces B (Spec (.of K)) hK)
    (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj M)) :
    nativeSection K B hK g p Φ hΦ M d =
      Functor.whiskerLeft Φ.op (classifierSection K g d) ≫
        (recoveryIso K g B hK p Φ hΦ M).hom := by
  simp only [nativeSection, originalSection, recoveryIso, Iso.trans_hom, Category.assoc]
  rfl

/-- Named native values retain the literal original classifier values. -/
theorem nativeValue_recovery (M : AlgebraicSpaces B (Spec (.of K)) hK)
    (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj M))
    (x : D) :
    nativeValue K B hK g p Φ hΦ M d x =
      ((recoveryIso K g B hK p Φ hΦ M).app (op x)).hom
        (d.value (Φ.obj x).base (Φ.obj x).family) := by
  rw [nativeValue, nativeSection_recovery]
  rfl

/-- Equality after native restriction is exactly equality on the same
original source family; there is no family-comparison assumption. -/
theorem nativeValue_eq_iff (M : AlgebraicSpaces B (Spec (.of K)) hK)
    (c d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj M))
    (x : D) :
    nativeValue K B hK g p Φ hΦ M c x = nativeValue K B hK g p Φ hΦ M d x ↔
      c.value (Φ.obj x).base (Φ.obj x).family = d.value (Φ.obj x).base (Φ.obj x).family := by
  rw [nativeValue_recovery, nativeValue_recovery]
  exact (ConcreteCategory.bijective_of_isIso _).1.eq_iff

private theorem whisker_transport {C : Type*} [Category C]
    {E : Type*} [Category E] {Q R : C ⥤ E} (h : Q = R)
    {M N : E ⥤ Type u} (f : M ⟶ N) :
    Functor.whiskerLeft Q f ≫ eqToHom (congrArg (fun q => q ⋙ N) h) =
      eqToHom (congrArg (fun q => q ⋙ M) h) ≫ Functor.whiskerLeft R f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Recovery commutes with every actual native algebraic-space map. -/
theorem recoveryIso_naturality {M N : AlgebraicSpaces B (Spec (.of K)) hK}
    (f : M ⟶ N) :
    Functor.whiskerLeft Φ.op (Functor.whiskerLeft (projection K g).op
        ((originalPresheafFunctor K B hK).map f)) ≫
        (recoveryIso K g B hK p Φ hΦ N).hom =
      (recoveryIso K g B hK p Φ hΦ M).hom ≫ Functor.whiskerLeft p.op f.hom := by
  have h := congrArg (fun q => q.op) hΦ
  have ht := whisker_transport h ((originalPresheafFunctor K B hK).map f)
  have hu := congrArg (Functor.whiskerLeft p.op)
    (originalNativeRestrictionSmallIso_naturality K B hK f)
  simp only [Functor.whiskerLeft_comp] at hu
  change Functor.whiskerLeft (Φ ⋙ projection K g).op
      ((originalPresheafFunctor K B hK).map f) ≫
      (eqToHom (congrArg (fun q => q ⋙ (originalPresheafFunctor K B hK).obj N) h) ≫
        Functor.whiskerLeft p.op
          (originalNativeRestrictionSmallIso K B hK N.obj N.property).hom) =
    (eqToHom (congrArg (fun q => q ⋙ (originalPresheafFunctor K B hK).obj M) h) ≫
      Functor.whiskerLeft p.op
        (originalNativeRestrictionSmallIso K B hK M.obj M.property).hom) ≫
      Functor.whiskerLeft p.op f.hom
  rw [← Category.assoc, ht, Category.assoc]
  change eqToHom _ ≫
      (Functor.whiskerLeft p.op (restrictMap K B hK ((originalPresheafFunctor K B hK).map f)) ≫
        Functor.whiskerLeft p.op
          (originalNativeRestrictionSmallIso K B hK N.obj N.property).hom) = _
  rw [hu, ← Category.assoc]

/-- Restriction commutes with actual target-map postcomposition. -/
theorem nativeSection_postcompose {M N : AlgebraicSpaces B (Spec (.of K)) hK}
    (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj M))
    (f : M ⟶ N) :
    nativeSection K B hK g p Φ hΦ N
        (postcompose K g d ((originalPresheafFunctor K B hK).map f)) =
      nativeSection K B hK g p Φ hΦ M d ≫ Functor.whiskerLeft p.op f.hom := by
  rw [nativeSection_recovery, classifierSection_postcompose, Functor.whiskerLeft_comp,
    Category.assoc, recoveryIso_naturality, ← Category.assoc, ← nativeSection_recovery]

/-- The same compatibility at each named object, with the literal native map. -/
theorem nativeValue_postcompose {M N : AlgebraicSpaces B (Spec (.of K)) hK}
    (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj M))
    (f : M ⟶ N) (x : D) :
    nativeValue K B hK g p Φ hΦ N
        (postcompose K g d ((originalPresheafFunctor K B hK).map f)) x =
      f.hom.app (op (p.obj x)) (nativeValue K B hK g p Φ hΦ M d x) := by
  rw [nativeValue, nativeSection_postcompose]
  rfl

end M9StacksIntegration.OriginalClassifierNativeCompatibility

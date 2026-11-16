module

public import M9StacksIntegration.AllTestClassifierSections
public import M9StacksIntegration.AllTestBoundedOriginalRecovery
public import M9StacksIntegration.AlgebraicSpaceValuedClassifierReflection

/-! A genuine original classifier gives a native discrete-target classifier.
The original-family functor and its structural base square are retained.
Its actual natural section is restricted using the proved native recovery
isomorphism, then read in the actual category of elements of the target.
No native classifier, comparison equivalence or compatibility is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9StacksIntegration.OriginalClassifierNativeRestriction
open AllTestOriginalFamilyCategory AllTestClassifierSections
  AllTestBoundedCharts AllTestBoundedRestriction AllTestNativeOriginalFunctor
  AllTestBoundedOriginalRecovery

universe u uD
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))
  (g : ℕ) {D : Type uD} [Category.{u} D]
  (p : D ⥤ BigFppfOver B (Spec (.of K)) hK)
  (Φ : D ⥤ CurveObject K g)
  (hΦ : Φ ⋙ projection K g = p ⋙ boundedInclusion B K hK)
  (M : AlgebraicSpaces B (Spec (.of K)) hK)
  (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj M))

/-- The terminal presheaf used for actual sections on the source category. -/
abbrev sectionSource : Dᵒᵖ ⥤ Type u := (Functor.const Dᵒᵖ).obj PUnit.{u+1}

/-- Restrict the actual original classifier section, with its true base
square transporting the section to the specified native bases. -/
def originalSection : sectionSource (D := D) ⟶
    p.op ⋙ (boundedInclusion B K hK).op ⋙
      (originalPresheafFunctor K B hK).obj M :=
  Functor.whiskerLeft Φ.op (classifierSection K g d) ≫ eqToHom (by
    change (Φ ⋙ projection K g).op ⋙ (originalPresheafFunctor K B hK).obj M =
      (p ⋙ boundedInclusion B K hK).op ⋙ (originalPresheafFunctor K B hK).obj M
    rw [hΦ])

/-- The target's actual recovery unit gives a genuine native section. -/
def nativeSection : sectionSource (D := D) ⟶ p.op ⋙ M.obj :=
  originalSection K B hK g p Φ hΦ M d ≫
    Functor.whiskerLeft p.op (originalNativeRestrictionSmallIso K B hK M.obj M.property).hom

/-- Actual named native values of the original classifier. -/
def nativeValue (x : D) : M.obj.obj (op (p.obj x)) :=
  (nativeSection K B hK g p Φ hΦ M d).app (op x) PUnit.unit

/-- Native naturality follows from the original classifier, not a supplied
map-invariance or native-classifier comparison premise. -/
theorem nativeValue_naturality {x y : D} (a : x ⟶ y) :
    M.obj.map (p.map a).op (nativeValue K B hK g p Φ hΦ M d y) =
      nativeValue K B hK g p Φ hΦ M d x := by
  have h := ConcreteCategory.congr_hom
    ((nativeSection K B hK g p Φ hΦ M d).naturality a.op) PUnit.unit
  exact h.symm

/-- The actual native target functor, keeping its literal native bases. -/
def targetFunctor : D ⥤
    (presheafOfCategories (M.obj ⋙ typeToCat)).obj where
  obj x := ⟨p.obj x, Discrete.mk (nativeValue K B hK g p Φ hΦ M d x)⟩
  map a := ⟨p.map a, Discrete.eqToHom
    (nativeValue_naturality K B hK g p Φ hΦ M d a).symm⟩
  map_id x := elements_hom_ext _ _ (p.map_id x)
  map_comp a b := elements_hom_ext _ _ (p.map_comp a b)

/-- The functor lies over exactly the original specified native base functor. -/
theorem targetFunctor_comp :
    targetFunctor K B hK g p Φ hΦ M d ⋙ discreteProjection M.obj = p := rfl

/-- The genuine native algebraic-space-valued based functor obtained from
the original all-family classifier. Its target is the actual native space. -/
def classifier : BasedCategory.ofFunctor p ⥤ᵇ
    M9Native.AlgebraicSpaceValuedClassifierReflection.target B (Spec (.of K)) hK M where
  toFunctor := targetFunctor K B hK g p Φ hΦ M d
  w := targetFunctor_comp K B hK g p Φ hΦ M d

/-- Naming its section recovers the actual constructed native value. -/
theorem classifier_namedValue (x : D) :
    sectionOfBasedFunctor (classifier K B hK g p Φ hΦ M d).toFunctor
      (classifier K B hK g p Φ hΦ M d).w x =
      nativeValue K B hK g p Φ hΦ M d x := rfl

end M9StacksIntegration.OriginalClassifierNativeRestriction

module

public import M9StacksIntegration.AllTestNativeOriginalSchemes
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Actual native pullbacks on the full original scheme category

The extension is left exact. Its proved natural comparison with the actual
original-space functor transports represented pullbacks without restricting
the original test schemes or changing any of the displayed scheme maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.AllTestNativeOriginalPullbacks
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalSchemes
  AllTestLargeSitePullback AllTestLargeSpaceGeometry

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Actual native pullback squares remain pullback squares on every
original test scheme under the actual original-space functor. -/
theorem original_isPullback
    {P X Y Z : AlgebraicSpaces B (Spec (.of K)) hK}
    (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a.hom b.hom f.hom g.hom) :
    IsPullback ((originalPresheafFunctor K B hK).map a)
      ((originalPresheafFunctor K B hK).map b)
      ((originalPresheafFunctor K B hK).map f)
      ((originalPresheafFunctor K B hK).map g) := by
  let J := BigFppfOver.topology B (Spec (.of K)) hK
  have hs : IsPullback ((nativeSheafFunctor K B hK).map a)
      ((nativeSheafFunctor K B hK).map b)
      ((nativeSheafFunctor K B hK).map f)
      ((nativeSheafFunctor K B hK).map g) := by
    apply IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type u))
    exact h
  have hl : IsPullback
      ((sheafCompose J uliftFunctor.{u+1, u}).map ((nativeSheafFunctor K B hK).map a))
      ((sheafCompose J uliftFunctor.{u+1, u}).map ((nativeSheafFunctor K B hK).map b))
      ((sheafCompose J uliftFunctor.{u+1, u}).map ((nativeSheafFunctor K B hK).map f))
      ((sheafCompose J uliftFunctor.{u+1, u}).map ((nativeSheafFunctor K B hK).map g)) := by
    apply IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type (u+1)))
    exact h.map ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u+1, u})
  letI : PreservesFiniteLimits (extendSheaf K B hK) :=
    extendSheaf_preservesFiniteLimits K B hK
  have he := (hl.map (extendSheaf K B hK)).map
      (sheafToPresheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1)))
  have he' : IsPullback ((extendedNativePresheafFunctor K B hK).map a)
      ((extendedNativePresheafFunctor K B hK).map b)
      ((extendedNativePresheafFunctor K B hK).map f)
      ((extendedNativePresheafFunctor K B hK).map g) := he
  let e := originalComparison K B hK
  have hw : IsPullback ((valueLift K).map ((originalPresheafFunctor K B hK).map a))
      ((valueLift K).map ((originalPresheafFunctor K B hK).map b))
      ((valueLift K).map ((originalPresheafFunctor K B hK).map f))
      ((valueLift K).map ((originalPresheafFunctor K B hK).map g)) := by
    apply he'.of_iso' (e.app P) (e.app X) (e.app Y) (e.app Z)
    · exact (e.hom.naturality a).symm
    · exact (e.hom.naturality b).symm
    · exact (e.hom.naturality f).symm
    · exact (e.hom.naturality g).symm
  letI : (valueLift K).Faithful := (valueLift_fullyFaithful K).faithful
  exact hw.of_map_of_faithful (valueLift K)

/-- An actual native represented chart is read as a map from the SAME
original scheme to the actual original-space image. -/
def originalChart (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj) :
    yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
      (originalPresheafFunctor K B hK).obj X :=
  (originalSchemeIso K B hK U).inv ≫
    (originalPresheafFunctor K B hK).map (ObjectProperty.homMk a)

/-- Actual represented native pullbacks give the literal corresponding
original represented square, including its original underlying scheme map. -/
theorem originalChart_isPullback
    {X Y : AlgebraicSpaces B (Spec (.of K)) hK}
    (f : X ⟶ Y) {V U : BigFppfOver B (Spec (.of K)) hK}
    (a : yoneda.obj V ⟶ X.obj) (b : V ⟶ U) (g : yoneda.obj U ⟶ Y.obj)
    (h : IsPullback a (yoneda.map b) f.hom g) :
    IsPullback (originalChart K B hK X V a)
      (yoneda.map ((boundedInclusion B K hK).map b))
      ((originalPresheafFunctor K B hK).map f)
      (originalChart K B hK Y U g) := by
  have hi := original_isPullback K B hK
    (ObjectProperty.homMk a : schemeSpace V ⟶ X)
    (schemeSpaceMap b) f (ObjectProperty.homMk g : schemeSpace U ⟶ Y) h
  apply hi.of_iso (originalSchemeIso K B hK V) (Iso.refl _)
    (originalSchemeIso K B hK U) (Iso.refl _)
  · simp [originalChart]
  · exact originalSchemeIso_naturality K B hK b
  · simp
  · simp [originalChart]

/-- The original chart construction retains actual postcomposition. -/
theorem originalChart_comp
    {X Y : AlgebraicSpaces B (Spec (.of K)) hK} (f : X ⟶ Y)
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj) :
    originalChart K B hK Y U (a ≫ f.hom) =
      originalChart K B hK X U a ≫ (originalPresheafFunctor K B hK).map f := by
  simp only [originalChart, Category.assoc, ← Functor.map_comp]
  rfl

end M9StacksIntegration.AllTestNativeOriginalPullbacks

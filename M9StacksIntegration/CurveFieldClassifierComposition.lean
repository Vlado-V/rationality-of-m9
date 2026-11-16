module

public import M9StacksIntegration.FiberedClassifierBaseChange
public import M9StacksIntegration.CurveFieldFamilyArrow
public import M9StacksIntegration.CurveClassifierPullback
public import M9StacksIntegration.NativeSchematicCurveCartesianArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme

/-!
# Actual original curve-family classifier composition

The original Cartesian family arrow is lifted to the genuine field stack.
The literal native OfFiberObj classifiers then compose up to the derived
two-isomorphism. Actual smoothness transfers through that comparison.
No classifier identity or smoothness of the source classifier is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u
namespace M9Native.CurveFieldClassifierComposition

open CurveFieldClassifyingFamily CurveFieldFamilyArrow

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {Q R : CurveFamily B hZ}
  (sQ : B.inclusion.obj Q.base.left ⟶ Spec (.of K))
  (sR : B.inclusion.obj R.base.left ⟶ Spec (.of K))
  (β : Q ⟶ R) (hβ : B.inclusion.map β.baseMap.left ≫ sR = sQ)

/-- The genuine field-family arrow gives the actual based classifier
composition isomorphism, with the ORIGINAL specified base objects. -/
def comparisonBasedIso :
    BasedFunctor.comp
      (Stack.overMapBased B (Spec (.of K)) hK (baseArrow B hZ hK sQ sR β hβ))
      (classifyingMor B hZ hK hAlg R sR).toBasedFunctor ≅
        (classifyingMor B hZ hK hAlg Q sQ).toBasedFunctor := by
  letI : (fieldStack B hZ hK hAlg).val.val.p.IsFibered :=
    (fieldStack B hZ hK hAlg).val.property.isFibered
  letI := arrow_isStronglyCartesian B hZ hK hAlg sQ sR β hβ
  exact FiberedClassifierBaseChange.comparisonBasedIso
    (fieldStack B hZ hK hAlg).val.val.p
    (fieldFamily_base B hZ hK hAlg Q sQ)
    (fieldFamily_base B hZ hK hAlg R sR)
    (baseArrow B hZ hK sQ sR β hβ) (arrow B hZ hK hAlg sQ sR β hβ)

/-- The same original family comparison in the native category fibred in
groupoids, as required by actual stack morphism properties. -/
def comparisonUnderlyingIso :
    (Stack.schemeStackMap.{u,u+1} B (Spec (.of K)) hK
      (baseArrow B hZ hK sQ sR β hβ) ≫ stackMorphism B hZ hK hAlg R sR).hom ≅
        (stackMorphism B hZ hK hAlg Q sQ).hom :=
  Bicategory.InducedBicategory.isoMk (comparisonBasedIso B hZ hK hAlg sQ sR β hβ)

/-- A genuine two-isomorphism preserves the actual native smooth-diagram
witness, without any representability or smoothness conclusion as input. -/
theorem isSmooth_of_underlyingIso {𝒳 𝒴 : Stack.AlgebraicStacks.{u,u+1} B (Spec (.of K)) hK}
    {f g : 𝒳 ⟶ 𝒴} (e : f.hom ≅ g.hom)
    (hf : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK f) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK g := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hasurj, hb, hsm⟩ := hf
  exact ⟨U, V, hU, hV, a, b, h, ⟨η ≪≫ Bicategory.whiskerLeftIso a e⟩,
    ha, hasurj, hb, hsm⟩

include hβ in
/-- A genuinely smooth ORIGINAL parameter map and genuinely smooth target
family classifier make the actual source family classifier smooth. The
composition identity is derived above from the real family arrow. -/
theorem source_classifier_isSmooth
    (hf : Smooth (B.inclusion.map β.baseMap.left))
    (hR : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (stackMorphism B hZ hK hAlg R sR)) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (stackMorphism B hZ hK hAlg Q sQ) := by
  apply isSmooth_of_underlyingIso B hK (comparisonUnderlyingIso B hZ hK hAlg sQ sR β hβ)
  exact Stack.AlgebraicStacks.isSmooth_comp.{u,u+1} B (Spec (.of K)) hK _ _
    (Stack.isSmooth_schemeStackMap.{u,u+1} B (Spec (.of K)) hK
      (baseArrow B hZ hK sQ sR β hβ) hf) hR

section OriginalSchemePullback

variable {X T P : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (hP : B.Contains P) (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (f : P ⟶ T) (hXP : B.Contains (CategoryTheory.Limits.pullback p f))
  (s : T ⟶ Spec (.of K))

/-- The actual original pullback square constructs the curve-family arrow;
no original-family arrow or model identification is supplied. -/
def pullbackFamilyArrow :
    CurveClassifierPullback.originalFamily B hZ hXP hP (CategoryTheory.Limits.pullback.snd p f) ⟶
      CurveClassifierPullback.originalFamily B hZ hX hT p :=
  NativeSchematicCurveCartesianArrow.arrow B hZ
    (CurveClassifierPullback.siteMap B hZ hX hT p)
    (CurveClassifierPullback.siteMap B hZ hXP hP (CategoryTheory.Limits.pullback.snd p f))
    (integerSiteMap B hZ hP hT f)
    (integerSiteMap B hZ hXP hX (CategoryTheory.Limits.pullback.fst p f))
    (by simpa only [CurveClassifierPullback.siteMap_toScheme] using
      (inferInstance : IsProper p))
    (by simpa only [CurveClassifierPullback.siteMap_toScheme] using
      (inferInstance : SmoothOfRelativeDimension 1 p))
    (by simpa only [CurveClassifierPullback.siteMap_toScheme] using
      (inferInstance : IsProper (CategoryTheory.Limits.pullback.snd p f)))
    (by simpa only [CurveClassifierPullback.siteMap_toScheme] using
      (inferInstance : SmoothOfRelativeDimension 1 (CategoryTheory.Limits.pullback.snd p f)))
    (by
      change IsPullback (CategoryTheory.Limits.pullback.fst p f)
        (CategoryTheory.Limits.pullback.snd p f) p f
      exact IsPullback.of_hasPullback p f)

/-- Its actual ground-field square is the original composite parameter map. -/
theorem pullbackFamilyArrow_ground :
    B.inclusion.map (pullbackFamilyArrow B hZ hX hT hP p f hXP).baseMap.left ≫ s =
      f ≫ s := rfl

/-- Actual smoothness of the original parameter morphism makes the actual
pullback family's classifier smooth. All original family data are constructed
above from the literal scheme-theoretic pullback. -/
theorem pullback_classifier_isSmooth [Smooth f]
    (hp : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (stackMorphism B hZ hK hAlg (CurveClassifierPullback.originalFamily B hZ hX hT p) s)) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (stackMorphism B hZ hK hAlg
        (CurveClassifierPullback.originalFamily B hZ hXP hP
          (CategoryTheory.Limits.pullback.snd p f)) (f ≫ s)) := by
  exact source_classifier_isSmooth B hZ hK hAlg
    (Q := CurveClassifierPullback.originalFamily B hZ hXP hP
      (CategoryTheory.Limits.pullback.snd p f))
    (R := CurveClassifierPullback.originalFamily B hZ hX hT p) (f ≫ s) s
    (pullbackFamilyArrow B hZ hX hT hP p f hXP)
    (pullbackFamilyArrow_ground B hZ hX hT hP p f hXP s)
    (inferInstance : Smooth f) hp

end OriginalSchemePullback

end M9Native.CurveFieldClassifierComposition

module

public import M9StacksIntegration.AtlasFieldFamilyClassifierComparison
public import M9StacksIntegration.SmoothGenusFieldStackInclusion
public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier

/-! Actual smooth-genus atlas families and their literal field classifiers.
The genuine smooth inclusion, original projected family, coefficient map,
and native two-isomorphism are all derived; algebraic-space totals are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
universe u
namespace M9Native.AtlasFamilyClassifierComparison

section GeneralAtlas

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)
  {V : BigFppfOver B (Spec (.of K)) hK}
  (a : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶
    M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg)

/-- The actual atlas map, followed by the proved native smooth genus inclusion. -/
def atlasMap : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶ wholeStack B hZ K hK :=
  a ≫ SmoothGenusFieldStackInclusion.inclusion B hZ K hK g hg

/-- The original projected atlas family, with its algebraic-space total retained. -/
abbrev atlasFamily : CurveFamily B hZ := family B hZ K hK (atlasMap B hZ K hK g hg a)

/-- This is the SAME original projected family in the chosen strict genus stack. -/
theorem atlasFamily_eq_nativeProjection :
    atlasFamily B hZ K hK g hg a =
      (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
        (a.hom.hom.toFunctor.obj (Functor.FiberedMor.unit V)) := by
  have h := Functor.congr_obj
    (congrArg (fun F => F ⋙ (curvesSmallEquivalenceOver B hZ).inv.functor)
      (SmoothGenusFieldStackInclusion.inclusion_smallProjection B hZ K hK g hg))
    (a.hom.hom.toFunctor.obj (Functor.FiberedMor.unit V))
  exact h

/-- Its actual coefficient structure map. -/
abbrev atlasStructure : B.inclusion.obj (atlasFamily B hZ K hK g hg a).base.left ⟶ Spec (.of K) :=
  structuralMap B hZ K hK (atlasMap B hZ K hK g hg a)

/-- The actual source object is derived from native basedness. -/
theorem atlasFamily_fieldBase : CurveFieldClassifyingFamily.fieldBase B hZ hK
    (atlasFamily B hZ K hK g hg a) (atlasStructure B hZ K hK g hg a) = V :=
  family_fieldBase B hZ K hK (atlasMap B hZ K hK g hg a)

/-- The literal original-family classifier and the genuine native atlas inclusion
agree through the derived isomorphism of their original source bases. -/
def atlasComparisonUnderlyingIso :
    (Stack.schemeStackMap.{u,u+1} B (Spec (.of K)) hK
      (baseIso B hZ K hK (atlasMap B hZ K hK g hg a)).hom ≫
        (a ≫ SmoothGenusFieldStackInclusion.inclusion B hZ K hK g hg)).hom ≅
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK (actualAlgebraicity B hZ)
        (atlasFamily B hZ K hK g hg a) (atlasStructure B hZ K hK g hg a)).hom :=
  comparisonUnderlyingIso B hZ K hK (atlasMap B hZ K hK g hg a)

/-- The literal original-family classifier is smooth, from the actual smooth
atlas and actual smooth genus inclusion. No classifier comparison is assumed. -/
theorem atlasClassifier_isSmooth
    (ha : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK a) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK (actualAlgebraicity B hZ)
        (atlasFamily B hZ K hK g hg a) (atlasStructure B hZ K hK g hg a)) :=
  classifier_isSmooth B hZ K hK (atlasMap B hZ K hK g hg a)
    (Stack.AlgebraicStacks.isSmooth_comp B (Spec (.of K)) hK a
      (SmoothGenusFieldStackInclusion.inclusion B hZ K hK g hg) ha
      (SmoothGenusFieldStackInclusion.inclusion_isSmooth B hZ K hK g hg))


end GeneralAtlas

end M9Native.AtlasFamilyClassifierComparison

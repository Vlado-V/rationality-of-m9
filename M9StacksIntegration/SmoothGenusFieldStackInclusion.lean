module

public import M9StacksIntegration.StrictNativeStackBaseChange
public import M9StacksIntegration.GenusNineCoarseOverField
public import M9StacksIntegration.CurveFieldClassifyingFamily

/-! The actual strict smooth-genus source maps to the original whole-Curves
field stack. Smoothness is a conclusion of the integer open immersion and
the proved native two-cartesian comparison. Original families and their
coefficient maps are preserved by the actual projection functors. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace M9Native.SmoothGenusFieldStackInclusion

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The actual native morphism from the strict field-base smooth genus
stack to the chosen whole-Curves field stack. Algebraicity is supplied by
the proved native Curves theorem, and no model comparison is an input. -/
def inclusion (g : ℕ) (hg : 2 ≤ g) :
    M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg ⟶
      CurveFieldClassifyingFamily.fieldStack B hZ hK
        (curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ) :=
  StrictNativeStackBaseChange.map B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).inclusion

/-- The actual source inclusion is an open immersion, derived by native
two-cartesian base change of the original genus-open immersion. -/
theorem inclusion_isOpenImmersion (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsOpenImmersion B (Spec (.of K)) hK
      (inclusion B hZ K hK g hg) :=
  StrictNativeStackBaseChange.map_isOpenImmersion B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).inclusion
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).isOpenImmersion

/-- In particular the same actual inclusion is smooth. -/
theorem inclusion_isSmooth (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK (inclusion B hZ K hK g hg) :=
  Stack.AlgebraicStacks.isSmooth_of_isOpenImmersion B (Spec (.of K)) hK _
    (inclusion_isOpenImmersion B hZ K hK g hg)

/-- Projection retains the same original small family and every original
arrow of that family, rather than substituting a classifier model. -/
theorem inclusion_smallProjection (g : ℕ) (hg : 2 ≤ g) :
    (inclusion B hZ K hK g hg).hom.hom.toFunctor ⋙
        CurveFieldClassifyingFamily.smallProjection B hZ hK
          (curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ) =
      StrictPullback.pr (Over.map (integerSiteObject B hZ hK).hom)
          (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p ⋙
        (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).inclusion.hom.hom.toFunctor :=
  StrictNativeStackBaseChange.map_original B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).inclusion

/-- The original coefficient-to-ground-field map survives literally. -/
theorem inclusion_base (g : ℕ) (hg : 2 ≤ g) :
    (inclusion B hZ K hK g hg).hom.hom.toFunctor ⋙
        (CurveFieldClassifyingFamily.fieldStack B hZ hK
          (curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ)).val.val.p =
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p :=
  (inclusion B hZ K hK g hg).hom.hom.w

end M9Native.SmoothGenusFieldStackInclusion

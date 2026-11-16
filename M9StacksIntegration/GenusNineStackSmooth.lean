module

public import M9StacksIntegration.GenusNineCoarseOverField
public import M9StacksIntegration.SmoothStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesSmoothness
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone

@[expose] public section

/-! Genuine structural smoothness and reducedness of the actual native smooth
curve stack.  Its name is not used as a smoothness premise: smoothness comes
from the proved deformation theorem for smooth curves and the actual open
locus, then from the strict native change-of-base square. -/

open CategoryTheory AlgebraicGeometry

namespace M9Native.GenusNineStackSmooth

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The original actual integer-base smooth cohomological-genus locus is
structurally smooth. -/
theorem integer_smooth (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
      (Stack.structureMorphism B integerBase hZ
        (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg)) := by
  have h : IsSmoothOverIntegers B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
      (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2) := by
    exact isSmoothOverIntegers_of_imp B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
      (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
      (C1590Private.isOpenCurvesLocus_isSmoothH0Family_of B hZ
        (C1590Private.isOpenCurvesLocus_hasUniversallyBijectiveGlobalFunctions_of
          (C1590Private.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
            (C1590Private.hasEtaleLocalSchemeCharts B hZ))
          (C1590Private.hasUniversallyBijectiveGlobalFunctions_of
            (C1590Private.hasEtaleLocalSchemeCharts B hZ))))
      (fun F hF => hF.1)
      (isSmoothOverIntegers_moduliSmoothCurves_and_moduliSmoothCurvesOfGenus.{u, u + 1}
        B hZ).1
  simpa only [IsSmoothOverIntegers, Stack.comp_structureMorphism,
    M9StacksIntegration.GenusNineCoarse.smoothStack,
    M9StacksIntegration.GenusNineCoarse.smoothOpen] using h

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- Smoothness is proved for the actual field-base stack of all the original
families, with no smoothness hypothesis on `Spec K → Spec ℤ`. -/
theorem smooth (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (Stack.structureMorphism B (Spec (.of K)) hK
        (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg)) :=
  SmoothStackBaseChange.smooth_changeOfBase B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg)
    (integer_smooth B hZ g hg)

/-- The actual native stack of smooth genus-`g` families over the original
field is reduced, as a conclusion of its structural smoothness. -/
theorem reduced (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsReducedStack B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg) :=
  SmoothStackBaseChange.reduced_over_field B K hK _ (smooth B hZ K hK g hg)

/-- The structural local-finite-type property is also derived from actual
smoothness, for application to the genuine coarse finite-type theorem. -/
theorem locallyFiniteType (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsLocallyOfFiniteType B (Spec (.of K)) hK
      (Stack.structureMorphism B (Spec (.of K)) hK
        (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg)) :=
  Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
    B (Spec (.of K)) hK
    (Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth
      B (Spec (.of K)) hK _ (smooth B hZ K hK g hg))

end M9Native.GenusNineStackSmooth

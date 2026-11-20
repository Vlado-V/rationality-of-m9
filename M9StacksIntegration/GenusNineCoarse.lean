module

public import M9StacksIntegration.GenusNineFiniteInertia
public import M9StacksIntegration.GenusNineCoarsePredicates
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSeparatedOfH2H3
public import StacksFrontier.AlgebraicGeometry.Quot.UniqueSmoothModelsScheme
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesInCurvesDM
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.KeelMoriTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import M9StacksIntegration.GenusNineSmoothCoarse

/-!
# Compatibility imports for the genus-g curve stacks

This module reexports the smooth and stable stack definitions and retains the separatedness,
finite inertia and coarse-space constructions for the stable stack.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.GenusNineCoarse

universe u w

section StableCurves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

theorem stableStack_separated (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (stableStack B hZ g)) := by
  simpa only [Stack.comp_structureMorphism] using
    isSeparated_moduliStableCurvesOfGenus_of_h2_h3 B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ) g hg
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2

theorem stableStack_finite_inertia (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsFinite B integerBase hZ
      (Stack.inertiaProjectionAlgebraicStacks B integerBase hZ (stableStack B hZ g)) :=
  finite_inertia_of_separated_quasiDM B integerBase hZ (stableStack B hZ g)
    (stableStack_separated B hZ g hg) (stableStack_quasiDM B hZ g hg)

/-- The full universal coarse-space existence result for the native stable-curve
stack. Finite inertia is proved, rather than included among the input hypotheses. -/
theorem exists_stableCoarseSpace (g : ℕ) (hg : 2 ≤ g) :
    ∃ (M : AlgebraicSpaces B integerBase hZ)
      (f : stableStack B hZ g ⟶ Stack.algebraicSpaceStack.{u, u + 1}
        B integerBase hZ M.obj M.property),
      Stack.IsUniformCategoricalModuliSpace B integerBase hZ M f.hom ∧
        Stack.AlgebraicStacks.IsSeparated B integerBase hZ f ∧
        Stack.IsQuasiCompactMorphism B integerBase hZ f ∧
        Stack.UniversalHomeomorphism B integerBase hZ f :=
  Stack.exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B integerBase hZ
    (stableStack B hZ g) (stableStack_finite_inertia B hZ g hg)

/-- A chosen native coarse algebraic space, selected from a proved universal
existence theorem. -/
def stableCoarseSpace (g : ℕ) (hg : 2 ≤ g) : AlgebraicSpaces B integerBase hZ :=
  (exists_stableCoarseSpace B hZ g hg).choose

def stableCoarseMap (g : ℕ) (hg : 2 ≤ g) :
    stableStack B hZ g ⟶ Stack.algebraicSpaceStack.{u, u + 1} B integerBase hZ
      (stableCoarseSpace B hZ g hg).obj (stableCoarseSpace B hZ g hg).property :=
  (exists_stableCoarseSpace B hZ g hg).choose_spec.choose

theorem stableCoarseMap_uniform (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsUniformCategoricalModuliSpace B integerBase hZ
      (stableCoarseSpace B hZ g hg) (stableCoarseMap B hZ g hg).hom :=
  (exists_stableCoarseSpace B hZ g hg).choose_spec.choose_spec.1

abbrev stableGenusNineCoarseSpace := stableCoarseSpace B hZ 9 (by decide)

/-- The actual base change of the native coarse algebraic space to `Spec K`,
implemented by restriction along the original map to the integer base. The
coarse universal-property comparison after this flat base change is separate. -/
def stableGenusNineCoarseSpaceOverField (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) : AlgebraicSpaces B (Spec (.of K)) hK :=
  ⟨(OverShriek.relocalizeRestrict (integerSiteObject B hZ hK).hom).obj
      (stableGenusNineCoarseSpace B hZ).obj,
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) integerBase hK hZ
      (integerSiteObject B hZ hK).hom _ (stableGenusNineCoarseSpace B hZ).property⟩

end StableCurves

end M9StacksIntegration.GenusNineCoarse

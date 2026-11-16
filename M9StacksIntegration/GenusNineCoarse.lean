module

public import M9StacksIntegration.GenusNineFiniteInertia
public import M9StacksIntegration.GenusNineCoarsePredicates
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSeparatedOfH2H3
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesInCurvesDM
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.KeelMoriTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase

/-!
The actual smooth and stable genus-g curve stacks and their genuine uniform
coarse algebraic spaces. Curves algebraicity, genus-locus openness, stable
separatedness and the actual DM locus are native proved inputs. Finite inertia
is derived from separatedness and quasi-DM, then Keel--Mori constructs the space.
No algebraicity, coarse-space, density or invariant-field premise is supplied.

Rational functions and smooth-in-stable density are separate later extensions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.GenusNineCoarse

universe u w

section StableCurves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The actual open substack of the stack of curve families cut out by stability
and the native cohomological genus condition. -/
abbrev stableOpen (g : ℕ) :=
  curvesSmallOpenSubstack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
    (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)

abbrev stableStack (g : ℕ) : Stack.AlgebraicStacks.{u, u + 1} B integerBase hZ :=
  (stableOpen B hZ g).toAlgebraicStack

/-- The actual smooth genus-`g` open substack inside the stable-curve stack. -/
abbrev smoothOpen (g : ℕ) (hg : 2 ≤ g) :=
  let _ := hg
  curvesSmallOpenSubstack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
    (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)

abbrev smoothStack (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.{u, u + 1} B integerBase hZ :=
  (smoothOpen B hZ g hg).toAlgebraicStack

theorem smooth_le_stable (g : ℕ) (hg : 2 ≤ g) :
    (smoothOpen B hZ g hg).property ≤ (stableOpen B hZ g).property := by
  apply curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ
    (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
    (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
    ?_ (curvesAlgebraicStack B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ))
    (curvesSmallEquivalence B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ))
    (curvesSmallEquivalence_functor_comp_p B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ))
  intro F hF
  exact stable_of_smooth_cohomological_genus B hZ hg hF

theorem stableStack_separated (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (stableStack B hZ g)) := by
  simpa only [Stack.comp_structureMorphism] using
    isSeparated_moduliStableCurvesOfGenus_of_h2_h3 B hZ
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ) g hg
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
      CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2

theorem stableStack_quasiDM (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiDMOver B integerBase hZ (stableStack B hZ g) := by
  let _ := hg
  obtain ⟨W, hW, hWdm, hstable, hgenus⟩ :=
    curvesSmall.exists_curvesDM_and_le_and_isDeligneMumfordStack_of_isOpenCurvesLocus
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ) g
      (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)
      (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
        CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
  have habs : Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ
      B.contains_terminal (stableStack B hZ g) := hgenus.2.1
  have hrel := Stack.AlgebraicStacks.isDMOver_of_isAbsolutelyDM B integerBase hZ
    B.contains_terminal (stableStack B hZ g) habs
  exact Stack.AlgebraicStacks.isQuasiDM_of_isDM B integerBase hZ hrel

theorem stableStack_finite_inertia (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsFinite B integerBase hZ
      (Stack.inertiaProjectionAlgebraicStacks B integerBase hZ (stableStack B hZ g)) :=
  finite_inertia_of_separated_quasiDM B integerBase hZ (stableStack B hZ g)
    (stableStack_separated B hZ g hg) (stableStack_quasiDM B hZ g hg)

/-- The actual inclusion of smooth families into stable families. -/
abbrev smoothToStable (g : ℕ) (hg : 2 ≤ g) :
    smoothStack B hZ g hg ⟶ stableStack B hZ g :=
  (stableOpen B hZ g).factor B integerBase hZ (smoothOpen B hZ g hg).inclusion
    (fun X => smooth_le_stable B hZ g hg _ X.property)

theorem smoothToStable_monomorphism (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsMonomorphism B integerBase hZ (smoothToStable B hZ g hg) := by
  let F := CatFiberedInGroupoids.homFunctor (smoothToStable B hZ g hg).hom
  let G := CatFiberedInGroupoids.homFunctor (stableOpen B hZ g).inclusion.hom
  have : G.Faithful := by
    change (ObjectProperty.ι _).Faithful
    infer_instance
  have : (F ⋙ G).Full := by
    change (ObjectProperty.ι _).Full
    infer_instance
  have : (F ⋙ G).Faithful := by
    change (ObjectProperty.ι _).Faithful
    infer_instance
  exact Stack.AlgebraicStacks.isMonomorphism_of_full_and_faithful B integerBase hZ
    (smoothToStable B hZ g hg) (Functor.Full.of_comp_faithful F G) (Functor.Faithful.of_comp F G)

theorem smoothStack_separated (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (smoothStack B hZ g hg)) := by
  have h := Stack.AlgebraicStacks.isSeparated_comp B integerBase hZ
    (smoothToStable B hZ g hg) (Stack.structureMorphism B integerBase hZ (stableStack B hZ g))
    (Stack.AlgebraicStacks.isSeparated_of_isMonomorphism B integerBase hZ
      (smoothToStable B hZ g hg) (smoothToStable_monomorphism B hZ g hg))
    (stableStack_separated B hZ g hg)
  simpa only [Stack.comp_structureMorphism] using h

theorem smoothStack_quasiDM (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiDMOver B integerBase hZ (smoothStack B hZ g hg) := by
  have h := Stack.AlgebraicStacks.isQuasiDM_comp B integerBase hZ
    (smoothToStable B hZ g hg) (Stack.structureMorphism B integerBase hZ (stableStack B hZ g))
    (Stack.AlgebraicStacks.isQuasiDM_of_isMonomorphism B integerBase hZ
      (smoothToStable B hZ g hg) (smoothToStable_monomorphism B hZ g hg))
    (stableStack_quasiDM B hZ g hg)
  simpa only [Stack.comp_structureMorphism] using h

theorem smoothStack_finite_inertia (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsFinite B integerBase hZ
      (Stack.inertiaProjectionAlgebraicStacks B integerBase hZ (smoothStack B hZ g hg)) :=
  finite_inertia_of_separated_quasiDM B integerBase hZ (smoothStack B hZ g hg)
    (smoothStack_separated B hZ g hg) (smoothStack_quasiDM B hZ g hg)

/-- Independently universal coarse-space existence for the actual smooth curve
stack. This is not the stable compactification named as the smooth moduli space. -/
theorem exists_smoothCoarseSpace (g : ℕ) (hg : 2 ≤ g) :
    ∃ (M : AlgebraicSpaces B integerBase hZ)
      (f : smoothStack B hZ g hg ⟶ Stack.algebraicSpaceStack.{u, u + 1}
        B integerBase hZ M.obj M.property),
      Stack.IsUniformCategoricalModuliSpace B integerBase hZ M f.hom ∧
        Stack.AlgebraicStacks.IsSeparated B integerBase hZ f ∧
        Stack.IsQuasiCompactMorphism B integerBase hZ f ∧
        Stack.UniversalHomeomorphism B integerBase hZ f :=
  Stack.exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B integerBase hZ
    (smoothStack B hZ g hg) (smoothStack_finite_inertia B hZ g hg)

def smoothCoarseSpace (g : ℕ) (hg : 2 ≤ g) : AlgebraicSpaces B integerBase hZ :=
  (exists_smoothCoarseSpace B hZ g hg).choose

def smoothCoarseMap (g : ℕ) (hg : 2 ≤ g) :
    smoothStack B hZ g hg ⟶ Stack.algebraicSpaceStack.{u, u + 1} B integerBase hZ
      (smoothCoarseSpace B hZ g hg).obj (smoothCoarseSpace B hZ g hg).property :=
  (exists_smoothCoarseSpace B hZ g hg).choose_spec.choose

theorem smoothCoarseMap_uniform (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsUniformCategoricalModuliSpace B integerBase hZ
      (smoothCoarseSpace B hZ g hg) (smoothCoarseMap B hZ g hg).hom :=
  (exists_smoothCoarseSpace B hZ g hg).choose_spec.choose_spec.1

/-- The independently universal coarse space of the actual smooth genus-nine
stack over the integer base. -/
abbrev smoothGenusNineCoarseSpace := smoothCoarseSpace B hZ 9 (by decide)

/-- Actual base change of the smooth coarse space. Its identification with the
coarse space of the base-changed smooth stack is a separate flat-base-change
comparison, not part of the algebraicity assertion used here. -/
def smoothGenusNineCoarseSpaceOverField (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) : AlgebraicSpaces B (Spec (.of K)) hK :=
  ⟨(OverShriek.relocalizeRestrict (integerSiteObject B hZ hK).hom).obj
      (smoothGenusNineCoarseSpace B hZ).obj,
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) integerBase hK hZ
      (integerSiteObject B hZ hK).hom _ (smoothGenusNineCoarseSpace B hZ).property⟩

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

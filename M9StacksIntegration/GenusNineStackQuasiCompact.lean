module

public import M9StacksIntegration.GenusNineCoarseOverField
public import M9StacksIntegration.OpenSubstackQuasiCompact
public import M9StacksIntegration.QuasiCompactStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition

@[expose] public section

/-! Actual boundedness and quasi-compactness of the smooth genus-g stack.
The stable-genus bounded family supplies compactness; local Noetherianity is
proved from actual limit preservation of Curves. The genuine smooth open and
strict field-base change are then used. No source-QC hypothesis is supplied.
-/

open CategoryTheory AlgebraicGeometry

namespace M9Native.GenusNineStackQuasiCompact

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Compactness of the actual stable cohomological-genus open, transferred
from the native bounded stable-curve family by its actual equivalence. -/
theorem stable_quasiCompact (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiCompactStack.{u, u+1} B integerBase hZ
      (M9StacksIntegration.GenusNineCoarse.stableStack B hZ g).val
      (M9StacksIntegration.GenusNineCoarse.stableStack B hZ g).property := by
  let h := curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ
  let hP := isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2
  letI := locallySmall_curveFamily B hZ
  letI := locallySmall_moduliStableCurvesOfGenus B hZ g
  let W := M9StacksIntegration.GenusNineCoarse.stableOpen B hZ g
  let E := curvesSmallEquivalence B hZ h
  let Phi : (moduliStableCurvesOfGenusSmall B hZ g).val ⥤ᵇ W.toAlgebraicStack.val.val :=
    { toFunctor := ShrinkHoms.inverse.{u} (moduliStableCurvesOfGenus B hZ g).val.obj ⋙
        ObjectProperty.lift W.property
          (ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) ⋙ E.functor) fun x =>
            (curvesSmallOpenSubstack_property_iff B hZ h hP x.obj).2
              ((isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus B hZ
                g x.obj).1 x.property)
      w := by
        change ShrinkHoms.inverse.{u} (moduliStableCurvesOfGenus B hZ g).val.obj ⋙
            ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) ⋙ E.functor ⋙
              (curvesAlgebraicStack B hZ h).val.val.p = _
        rw [curvesSmallEquivalence_functor_comp_p]
        rfl }
  have hsurj : Function.Surjective (Stack.pointsMap B integerBase hZ
      (moduliStableCurvesOfGenusSmall B hZ g).val
      (moduliStableCurvesOfGenusSmall B hZ g).property W.toAlgebraicStack.val.property Phi) := by
    refine Quotient.ind fun q => ?_
    refine ⟨Stack.pointClass B integerBase hZ _ (moduliStableCurvesOfGenusSmall B hZ g).property
      { carrier := q.carrier
        field := q.field
        base := q.base
        isSpec := q.isSpec
        obj := ShrinkHoms.toShrinkHoms (⟨E.inverse.obj q.obj.obj,
          (isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus B hZ g _).2
            ((curvesOpenSubstackOfIsOpenCurvesLocus_property_iff_inverse B hZ hP _ _
              (curvesSmallEquivalence_functor_comp_p B hZ h) q.obj.obj).1 q.obj.property)⟩ :
            ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g))
        «over» := q.over }, rfl⟩
  exact @Function.Surjective.compactSpace _ _
    (Stack.pointTopology B integerBase hZ (moduliStableCurvesOfGenusSmall B hZ g))
    (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val) _
    (Stack.continuous_pointsMap B integerBase hZ (moduliStableCurvesOfGenusSmall B hZ g)
      W.toAlgebraicStack.val Phi)
    (compactSpace_points_moduliStableCurvesOfGenusSmall B hZ g hg) hsurj

/-- Local Noetherianity of the actual stable locus comes from the actual
Curves limit-preservation theorem, not from a property assumption on the locus. -/
theorem stable_locallyNoetherian (g : ℕ) :
    Stack.HasPropertyOnSomeSchemeAtlas B integerBase hZ
      (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (M9StacksIntegration.GenusNineCoarse.stableStack B hZ g) := by
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  let h := curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ
  let W := M9StacksIntegration.GenusNineCoarse.stableOpen B hZ g
  have hwhole : Stack.AlgebraicStacks.IsLocallyOfFiniteType B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
    Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
      (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h
        (C1590Private.isLimitPreserving_curvesFiberedCategory B hZ))
  have hW : Stack.AlgebraicStacks.IsLocallyOfFiniteType B integerBase hZ
      (Stack.structureMorphism B integerBase hZ W.toAlgebraicStack) := by
    simpa only [Stack.comp_structureMorphism] using
      Stack.AlgebraicStacks.isLocallyOfFiniteType_comp B integerBase hZ W.inclusion _
        (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
          B integerBase hZ
          (Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isOpenImmersion
            B integerBase hZ W.inclusion W.isOpenImmersion)) hwhole
  apply Stack.AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B integerBase hZ _ hW
  apply (Stack.exists_scheme_atlas_iff_scheme B integerBase hZ
    (fun T : Scheme.{u} => IsLocallyNoetherian T)
    (Over.mk (𝟙 (B.obj hZ)))).2
  change IsLocallyNoetherian integerBase
  infer_instance

/-- Quasi-compactness of the genuine smooth cohomological-genus open follows
from its actual inclusion in the bounded locally Noetherian stable open. -/
theorem integer_quasiCompact (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiCompactStack.{u, u+1} B integerBase hZ
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).property :=
  OpenSubstackQuasiCompact.quasiCompact_of_le B integerBase hZ
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg)
    (M9StacksIntegration.GenusNineCoarse.stableOpen B hZ g)
    (M9StacksIntegration.GenusNineCoarse.smooth_le_stable B hZ g hg)
    (stable_quasiCompact B hZ g hg) (stable_locallyNoetherian B hZ g)

/-- The actual field-base stack is quasi-compact on all original families. -/
theorem quasiCompact (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    (g : ℕ) (hg : 2 ≤ g) :
    Stack.IsQuasiCompactStack.{u, u+1} B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).property :=
  QuasiCompactStackBaseChange.quasiCompact_changeOfBase B (Spec (.of K)) integerBase hK hZ
    (integerSiteObject B hZ hK).hom inferInstance inferInstance
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg)
    (integer_quasiCompact B hZ g hg)

end M9Native.GenusNineStackQuasiCompact

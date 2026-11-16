module

public import M9StacksIntegration.FixedDegreeCoverScheme
public import M9StacksIntegration.GraphHilbertEulerComparison
public import M9StacksIntegration.CurveClassifierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleRelativeAmpleTransfer

/-! Actual five cover schemes of original polarized relative curves.
Native family properties and native ample modules are derived from the
original source and target maps and their genuine original polarizations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace M9Native.PolarizedCurveCoverScheme

open GraphHilbertEulerComparison

variable (B : BigFppfSite.{u})
  {Z X T : Scheme.{u}} (hZ : B.Contains Z) (hX : B.Contains X) (hT : B.Contains T)
  (z : Z ⟶ T) (x : X ⟶ T)
  [IsProper z] [SmoothOfRelativeDimension 1 z]
  [IsProper x] [SmoothOfRelativeDimension 1 x]

abbrev sourceSite := integerSiteObject B (B.contains_integerBase) hZ
abbrev targetSite := integerSiteObject B (B.contains_integerBase) hX
abbrev baseSite := integerSiteObject B (B.contains_integerBase) hT
abbrev sourceMap := integerSiteMap B (B.contains_integerBase) hZ hT z
abbrev targetMap := integerSiteMap B (B.contains_integerBase) hX hT x

abbrev sourceFamily :=
  CurveClassifierPullback.originalFamily B (B.contains_integerBase) hZ hT z
abbrev targetFamily :=
  CurveClassifierPullback.originalFamily B (B.contains_integerBase) hX hT x

abbrev sourceAlgebraic := isAlgebraicSpace_yoneda B integerBase (B.contains_integerBase) (sourceSite B hZ)
abbrev targetAlgebraic := isAlgebraicSpace_yoneda B integerBase (B.contains_integerBase) (targetSite B hX)
abbrev baseAlgebraic := isAlgebraicSpace_yoneda B integerBase (B.contains_integerBase) (baseSite B hT)

/-- Native source properness is read from the real original curve family. -/
theorem sourceProper : Space.IsProper B integerBase (B.contains_integerBase)
    (yoneda.map (sourceMap B hZ hT z)) :=
  (sourceFamily B hZ hT z).proper

theorem sourceFlat : Space.IsFlat B integerBase (B.contains_integerBase)
    (yoneda.map (sourceMap B hZ hT z)) :=
  (sourceFamily B hZ hT z).flat

theorem sourceFinitePresentation : Space.IsFinitePresentation B integerBase (B.contains_integerBase)
    (yoneda.map (sourceMap B hZ hT z)) :=
  (sourceFamily B hZ hT z).finitePresentation

theorem targetSeparated : Space.IsSeparated B integerBase (B.contains_integerBase)
    (yoneda.map (targetMap B hX hT x)) :=
  (targetFamily B hX hT x).proper.1

theorem targetFinitePresentation : Space.IsFinitePresentation B integerBase (B.contains_integerBase)
    (yoneda.map (targetMap B hX hT x)) :=
  (targetFamily B hX hT x).finitePresentation

variable (N : Z.Modules)
  [hN : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.property N]
  (L : X.Modules)
  [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]

abbrev sourceLine : Space.Modules.{u,u} B integerBase (B.contains_integerBase)
    (yoneda.obj (sourceSite B hZ)) (sourceAlgebraic B hZ) :=
  associatedModule B integerBase (B.contains_integerBase) (sourceSite B hZ) N

abbrev targetLine : Space.Modules.{u,u} B integerBase (B.contains_integerBase)
    (yoneda.obj (targetSite B hX)) (targetAlgebraic B hX) :=
  associatedModule B integerBase (B.contains_integerBase) (targetSite B hX) L

instance sourceLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase (B.contains_integerBase) (yoneda.obj (sourceSite B hZ)))
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase (B.contains_integerBase)
          (yoneda.obj (sourceSite B hZ)) (sourceAlgebraic B hZ)).O).property
      (sourceLine B hZ N) :=
  isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
    B integerBase (B.contains_integerBase) (sourceSite B hZ) N
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN)

instance targetLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase (B.contains_integerBase) (yoneda.obj (targetSite B hX)))
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase (B.contains_integerBase)
          (yoneda.obj (targetSite B hX)) (targetAlgebraic B hX)).O).property
      (targetLine B hX L) :=
  isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
    B integerBase (B.contains_integerBase) (targetSite B hX) L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)

/-- The actual graph-Hilbert locus uses the actual associated original lines. -/
abbrev coverLocus (d : ℕ) :=
  FixedDegreeCoverSpace.coverLocus (sourceAlgebraic B hZ) (targetAlgebraic B hX)
    (baseAlgebraic B hT) (targetSeparated B hX hT x) (targetFinitePresentation B hX hT x)
    (sourceFinitePresentation B hZ hT z) (sourceFlat B hZ hT z) (sourceProper B hZ hT z)
    (sourceLine B hZ N) (targetLine B hX L) d

abbrev coverProjection (d : ℕ) :=
  FixedDegreeCoverSpace.coverProjection (sourceAlgebraic B hZ) (targetAlgebraic B hX)
    (baseAlgebraic B hT) (targetSeparated B hX hT x) (targetFinitePresentation B hX hT x)
    (sourceFinitePresentation B hZ hT z) (sourceFlat B hZ hT z) (sourceProper B hZ hT z)
    (sourceLine B hZ N) (targetLine B hX L) d

/-- Five actual finite-type representing schemes are constructed from
original polarized relative curves over the original affine base. -/
theorem exists_five_coverSchemes [IsAffine T]
    (hNa : Stacks.RelativeAmple.IsRelativelyAmple z N)
    (hLa : Stacks.RelativeAmple.IsRelativelyAmple x L) :
    ∃ (Y : Fin 5 → BigFppfOver B integerBase (B.contains_integerBase))
      (a : ∀ i, yoneda.obj (Y i) ⟶
        (coverLocus B hZ hX hT z x N L (BoundedPencilGraphPolynomial.degreeIndex i)).toFunctor)
      (q : ∀ i, Y i ⟶ baseSite B hT),
      (∀ i, IsIso (a i)) ∧
      (∀ i, a i ≫ coverProjection B hZ hX hT z x N L
        (BoundedPencilGraphPolynomial.degreeIndex i) = yoneda.map (q i)) ∧
      (∀ i, QuasiCompactFiniteType
        ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map (q i))) := by
  letI : IsAffine ((BigFppfOver.toScheme B integerBase (B.contains_integerBase)).obj
      (baseSite B hT)) := by
    change IsAffine T
    infer_instance
  have hNa' := isRelativelyAmple_schemeSpaceMap_associatedModule
    (sourceMap B hZ hT z) N hNa
  have hLa' := isRelativelyAmple_schemeSpaceMap_associatedModule
    (targetMap B hX hT x) L hLa
  exact FixedDegreeCoverScheme.exists_five_coverSchemes (baseSite B hT)
    (sourceAlgebraic B hZ) (targetAlgebraic B hX) (baseAlgebraic B hT)
    (targetSeparated B hX hT x) (targetFinitePresentation B hX hT x)
    (sourceFinitePresentation B hZ hT z) (sourceFlat B hZ hT z) (sourceProper B hZ hT z)
    (sourceLine B hZ N) (targetLine B hX L) hNa' hLa'

end M9Native.PolarizedCurveCoverScheme
end

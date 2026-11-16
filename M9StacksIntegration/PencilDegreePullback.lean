module

public import M9StacksIntegration.PencilPullbackSections
public import M9StacksIntegration.LinearSeriesFromCohomology
public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor

/-!
# Genuine pencils pulled back by a nonconstant curve map

The degree is the native extension degree of function fields. For a
degree-one line on the target with two sections, native pullback degree
and the actual injective cohomology pullback construct a native pencil
whose degree is the map degree. Adding a genuine effective divisor then
pads every smaller degree. All curve morphism instances are derived
from the actual structural square and nonconstancy.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.PencilDegreePullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable [IsCurve k pX] [IsCurve k pY]

/-- The native degree of the actual nonconstant morphism, with the
required morphism instances genuinely derived from the original square. -/
def curveMapDegree (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) : ℕ :=
  @degreeOver X Y g inferInstance inferInstance
    (locallyOfFiniteType_of_isCurve_comp k pX pY g hg)
    (isDominant_of_not_constant k pX pY g hnc)

/-- Nonconstancy of the original proper-curve morphism gives actual
finiteness; no finite-map premise is required in the final interface. -/
theorem curveMap_isFinite [IsProper pX] [IsProper pY]
    (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) : IsFinite g :=
  isFinite_of_not_constant k pX pY g hg hnc

variable [IsProper pX] [IsProper pY]

omit [IsProper pY] in
/-- Actual line-bundle sections pull back injectively on native H0,
so the section count cannot drop. -/
theorem h0_le_pullback (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M] :
    Module.finrank k (cohomologyOverField k pY M 0) ≤
      Module.finrank k (cohomologyOverField k pX ((Scheme.Modules.pullback g).obj M) 0) := by
  subst hg
  let := isDominant_of_not_constant k (g ≫ pY) pY g hnc
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g M
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pY)
  let : ((Scheme.Modules.pullback g).obj M).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
  let := finiteDimensional_cohomologyOverField_of_isProper k (g ≫ pY)
    ((Scheme.Modules.pullback g).obj M) 0
  exact LinearMap.finrank_le_finrank_of_injective
    (PencilPullbackSections.cohomologyPullback_injective k pY g M)

/-- Native pullback degree at an actual degree-one target line computes
the original function-field degree, rather than a replacement notion. -/
theorem pullback_degree_eq_curveMapDegree
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M]
    (hM : invertibleCurveDegree k pY hdimY M = 1) :
    letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj M) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback g M
    invertibleCurveDegree k pX hdimX ((Scheme.Modules.pullback g).obj M) =
      (curveMapDegree pX pY g hg hnc : ℤ) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} M 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible Y M
  let := isFiniteLocallyFreeOfRank_pullback g M 1
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g M
  have h := curveDegree_pullback_eq_degreeOver_mul k pX pY g hg hnc M 1
  have hM' : curveDegree k pY hdimY M 1 = 1 := by
    rw [← invertibleCurveDegree_eq_curveDegree_one]
    exact hM
  rw [hM', mul_one] at h
  rw [invertibleCurveDegree_eq_curveDegree_one]
  exact h

/-- An actual degree-one target line with two sections gives a native
pencil of exactly the original nonconstant morphism's field degree. -/
theorem nonempty_pencil_of_curveMap
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M]
    (hM : invertibleCurveDegree k pY hdimY M = 1)
    (h0 : 2 ≤ Module.finrank k (cohomologyOverField k pY M 0)) :
    Nonempty (LinearSeries k pX hdimX (curveMapDegree pX pY g hg hnc) 1) := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g M
  exact LinearSeriesFromCohomology.nonempty_linearSeries_of_finrank_H0 k pX hdimX
    ((Scheme.Modules.pullback g).obj M) (curveMapDegree pX pY g hg hnc) 1
    (pullback_degree_eq_curveMapDegree pX pY hdimX hdimY g hg hnc M hM)
    (h0.trans (h0_le_pullback pX pY g hg hnc M))

/-- Padding by an actual effective divisor includes all lower map
degrees in the original degree-N pencil predicate. -/
theorem nonempty_pencil_of_curveMap_degree_le [IsAlgClosed k] [Smooth pX]
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M]
    (hM : invertibleCurveDegree k pY hdimY M = 1)
    (h0 : 2 ≤ Module.finrank k (cohomologyOverField k pY M 0))
    (N : ℕ) (hdeg : curveMapDegree pX pY g hg hnc ≤ N) :
    Nonempty (LinearSeries k pX hdimX N 1) :=
  M9StacksIntegration.LinearSeriesAddEffectiveDivisor.nonempty_linearSeries_of_degree_le
    pX hdimX (nonempty_pencil_of_curveMap pX pY hdimX hdimY g hg hnc M hM h0) hdeg

end M9Native.PencilDegreePullback

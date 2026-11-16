module

public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineProperties
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree

/-!
# A genuine degree-one line with two sections on the native projective line

The genus-zero calculation is transported from the polynomial model by
the actual coordinate-pinned comparison isomorphism. On the relative
model an actual rational point divisor gives a degree-one line; native
Riemann--Roch supplies its two sections. No degree-one line, its section
count, or model-comparison cohomology equality is supplied as data.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

universe u

namespace M9Native.PencilProjectiveLineGeometry

attribute [local instance] isCurve_projectiveSpaceOver_one
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual native relative projective line. -/
abbrev Line (k : Type u) [Field k] : Scheme.{u} := projectiveSpaceOver 1 (Spec (.of k))

/-- Its original structure morphism. -/
abbrev toBase (k : Type u) [Field k] : Line k ⟶ Spec (.of k) :=
  projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)

theorem lineDimension (k : Type u) [Field k] : topologicalKrullDim (Line k) ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := k) (f := toBase k)).le

/-- The genus of the actual relative model is zero, using genuine
cohomology transport through the native polynomial comparison. -/
theorem genus_line_eq_zero (k : Type u) [Field k] : genus (toBase k) = 0 := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  have hbase : c.iso.hom ≫ projToSpecCoeff k 1 = toBase k := c.toBase
  have hcoh := finrank_cohomologyOverField_unit_pushforward k c.iso.hom
    (projToSpecCoeff k 1) 1
  have hgcomp : genus (c.iso.hom ≫ projToSpecCoeff k 1) = genus (projToSpecCoeff k 1) := by
    rw [← finrank_cohomologyOverField_one_unit_eq_genus k (c.iso.hom ≫ projToSpecCoeff k 1),
      ← finrank_cohomologyOverField_one_unit_eq_genus k (projToSpecCoeff k 1)]
    exact hcoh
  calc
    genus (toBase k) = genus (c.iso.hom ≫ projToSpecCoeff k 1) :=
      congrArg (fun q : Line k ⟶ Spec (.of k) => genus q) hbase.symm
    _ = genus (projToSpecCoeff k 1) := hgcomp
    _ = 0 := Stacks.Curves.genus_projToSpecCoeff_one k

/-- The actual degree-one point divisor on P1 supplies a line with two
native cohomology sections. In particular these are constructed geometric
data, not an input to the reverse pencil--map implication. -/
theorem exists_degreeOne_line_with_two_sections (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ (M : (Line k).Modules)
      (hM : SheafOfModules.IsInvertible (Line k).presheaf (Line k).ringCatSheaf.property M),
      letI := hM
      invertibleCurveDegree k (toBase k) (lineDimension k) M = 1 ∧
        2 ≤ Module.finrank k (cohomologyOverField k (toBase k) M 0) := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  let : Smooth (toBase k) := smooth_of_iso_projectiveLine (toBase k) c.iso c.toBase
  obtain ⟨D, hD, hd⟩ :=
    M9StacksIntegration.LinearSeriesAddEffectiveDivisor.exists_effective_point_degree_one
      (toBase k) (lineDimension k)
  let := hD
  let M : (Line k).Modules := Stacks.Divisors.invertibleSheaf' D
  let hM : SheafOfModules.IsInvertible (Line k).presheaf (Line k).ringCatSheaf.property M :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  let := hM
  let : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (toBase k).appTop) :=
    isIso_globalSections_of_iso_projectiveLine (toBase k) c.iso c.toBase
  refine ⟨M, hM, hd, ?_⟩
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k (toBase k)
    (lineDimension k) M
  rw [hd, genus_line_eq_zero k] at h
  omega

end M9Native.PencilProjectiveLineGeometry

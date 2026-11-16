module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIdeal
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenusExplicit
public import Mathlib.Tactic

/-!
# Genus nine excludes a native plane closed immersion

The obstruction uses the actual cohomological genus and the actual homogeneous
equation extracted from the closed immersion. The plane-genus arithmetic is
proved for every possible equation degree, including the small-degree cases
with truncated natural-number subtraction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace M9StacksIntegration.GenusNineNotPlane

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- No homogeneous plane equation has arithmetic genus nine. -/
theorem plane_genus_ne_nine (n : ℕ) : (n - 1) * (n - 2) / 2 ≠ 9 := by
  intro h
  have hp : (n - 1) * (n - 2) < 20 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < (2 : ℕ))).mp
      (show (n - 1) * (n - 2) / 2 < 10 by omega)
  have hn : n < 6 := by
    by_contra hn
    have h1 : 5 ≤ n - 1 := by omega
    have h2 : 4 ≤ n - 2 := by omega
    have hprod := Nat.mul_le_mul h1 h2
    omega
  interval_cases n <;> norm_num at h

/-- Reducedness supplies the native absence of embedded associated points. -/
theorem reduced_hasNoEmbeddedPoints (X : Scheme.{u}) [IsReduced X] :
    HasNoEmbeddedPoints X := by
  intro x hx
  obtain ⟨hx, y, _hy, hyx, hne⟩ := hx
  have hxw : x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X :=
    associatedPoints_subset_weaklyAssociatedPoints (SheafOfModules.unit X.ringCatSheaf) hx
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints X] at hxw
  exact hne (Topology.eq_of_specializes_isGenericPoint hxw isGenericPoint_closure hyx)

/-- The single irreducible component of a curve has its actual dimension one. -/
theorem irreducible_components_dimension_one (X : Scheme.{u}) [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 1) :
    ∀ W ∈ irreducibleComponents X, topologicalKrullDim W = 1 := by
  intro W hW
  have hW' : W = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hW
  subst W
  exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq.trans hdim

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A reduced irreducible native plane curve cannot have actual genus nine.
The equation and its unrestricted degree are obtained from the closed immersion. -/
theorem genus_ne_nine_of_planeClosedImmersion [IsReduced X] [IrreducibleSpace X]
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X = 1) :
    genus (i ≫ projToSpecCoeff k 2) ≠ 9 := by
  have hno := reduced_hasNoEmbeddedPoints X
  have hequidim := irreducible_components_dimension_one X hdim
  obtain ⟨_d, F, _hhom, hF⟩ :=
    projectivePlane_exists_homogeneous_eq_idealOfClosedSubscheme k i hno hequidim
  rw [genus_eq_of_explicit i hno hdim hequidim F hF]
  exact plane_genus_ne_nine F.totalDegree

/-- The actual genus-nine curve admits no closed immersion into the native
projective plane over its original field. In particular this applies to every
proper smooth genus-nine curve. -/
theorem not_isClosedImmersion_of_genus_nine (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (hg : genus f = 9)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    (hi : i ≫ projToSpecCoeff k 2 = f) : ¬ IsClosedImmersion i := by
  intro hclosed
  let := hclosed
  have h := genus_ne_nine_of_planeClosedImmersion i
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))
  rw [hi] at h
  exact h hg

theorem no_plane_closedImmersion (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (hg : genus f = 9) :
    ¬ ∃ i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k),
      IsClosedImmersion i ∧ i ≫ projToSpecCoeff k 2 = f := by
  rintro ⟨i, hclosed, hi⟩
  exact not_isClosedImmersion_of_genus_nine f hg i hi hclosed

/-- The same obstruction for an actual morphism in the category over Spec k. -/
theorem not_isClosedImmersion_over_of_genus_nine (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (hg : genus f = 9)
    (i : Over.mk f ⟶ Over.mk (projToSpecCoeff k 2)) :
    ¬ IsClosedImmersion i.left :=
  not_isClosedImmersion_of_genus_nine f hg i.left i.w

end M9StacksIntegration.GenusNineNotPlane

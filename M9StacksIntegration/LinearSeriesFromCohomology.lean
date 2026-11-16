module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import Mathlib.Tactic

/-!
# Actual section subspaces and the native linear-series existence test

An actual invertible sheaf of degree `d` with at least `r+1` actual H0
sections produces an actual native linear series, by constructing its
section subspace. In particular, nonexistence of a degree-eight net over
the stated base field bounds H0 of every actual degree-eight sheaf over
that same field by two. No extension-field conclusion is asserted.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace M9Native.LinearSeriesFromCohomology

variable (k : Type u) [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)

/-- Construct the actual section submodule of the native linear series
from an actual H0 dimension bound. -/
theorem nonempty_linearSeries_of_finrank_H0 (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (d r : ℕ) (hdeg : invertibleCurveDegree k f hdim L = (d : ℤ))
    (hsections : r+1 ≤ Module.finrank k (cohomologyOverField k f L 0)) :
    Nonempty (LinearSeries k f hdim d r) := by
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank hsections
  refine ⟨{
    L := L
    isInvertible := inferInstance
    degree_eq := hdeg
    V := Submodule.span k (Set.range s)
    finrank_eq := ?_ }⟩
  simpa only [Fintype.card_fin] using finrank_span_eq_card hs

/-- Failure of the actual native base-field net-existence statement
forces the actual H0 bound on each actual degree-eight invertible sheaf
over that field. -/
theorem finrank_H0_le_two_of_no_degree_eight_net
    (hno : ¬ Nonempty (LinearSeries k f hdim 8 2)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : invertibleCurveDegree k f hdim L = 8) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 2 := by
  by_contra h
  have hb : 2+1 ≤ Module.finrank k (cohomologyOverField k f L 0) := by omega
  exact hno (nonempty_linearSeries_of_finrank_H0 k f hdim L 8 2 hdeg hb)

end M9Native.LinearSeriesFromCohomology

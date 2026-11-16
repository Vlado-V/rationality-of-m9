module

public import M9StacksIntegration.MukaiSemiIrreducible
public import M9StacksIntegration.LinearSeriesFromCohomology
public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# The actual low-degree-pencil obstruction in Mukai Proposition 5.3

Two genuine independent sections of an invertible sheaf give a native
linear series. Its degree is nonnegative by the actual section-degree
theorem. Adding a constructed effective divisor then turns every pencil
of degree at most five into a degree-five pencil. Consequently the three
actual quotient line bundles in Mukai's argument, if each has two
sections, have total degree at least eighteen, and cannot have total
degree sixteen.

This file proves that obstruction from the actual no-degree-five-pencil
condition. It does not supply or assume the stronger Clifford-index-four
inequalities used elsewhere in the semi-irreducibility proof.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace M9Native.MukaiPencilDegreeBounds

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- On an actual nonpentagonal curve, every genuine line bundle with two
independent global sections has native degree at least six. -/
theorem six_le_degree_of_two_sections
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h0 : 2 ≤ Module.finrank k (cohomologyOverField k f L 0)) :
    (6 : ℤ) ≤ invertibleCurveDegree k f hdim L := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank h0
  let s := MukaiSemiIrreducible.sectionOfH0 k f L (v 0)
  have hs : s.eval (op ⊤) ≠ 0 := by
    rw [MukaiSemiIrreducible.sectionOfH0_eval_top]
    intro hz
    apply hv.ne_zero 0
    have hh := congrArg (fun t => (cohomologyOverFieldZeroLinearIso k f L).inv t) hz
    simpa only [Iso.hom_inv_id_apply, map_zero] using hh
  have hnn := invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim L s hs
  let d := (invertibleCurveDegree k f hdim L).toNat
  have hd : invertibleCurveDegree k f hdim L = (d : ℤ) :=
    (Int.toNat_of_nonneg hnn).symm
  by_contra h
  have h5 : d ≤ 5 := by omega
  apply hnp
  exact M9StacksIntegration.LinearSeriesAddEffectiveDivisor.nonempty_linearSeries_of_degree_le
    f hdim
    (LinearSeriesFromCohomology.nonempty_linearSeries_of_finrank_H0
      k f hdim L d 1 hd h0) h5

/-- The three-line-bundle contradiction in Mukai Proposition 5.3 uses
their original native degrees and actual cohomology spaces. -/
theorem degree_sum_ne_sixteen_of_two_sections
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (L M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hL : 2 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (hM : 2 ≤ Module.finrank k (cohomologyOverField k f M 0))
    (hN : 2 ≤ Module.finrank k (cohomologyOverField k f N 0)) :
    invertibleCurveDegree k f hdim L + invertibleCurveDegree k f hdim M +
      invertibleCurveDegree k f hdim N ≠ 16 := by
  have hLd := six_le_degree_of_two_sections f hdim hnp L hL
  have hMd := six_le_degree_of_two_sections f hdim hnp M hM
  have hNd := six_le_degree_of_two_sections f hdim hnp N hN
  omega

end M9Native.MukaiPencilDegreeBounds

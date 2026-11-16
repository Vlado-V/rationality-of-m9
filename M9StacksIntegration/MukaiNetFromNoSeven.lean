module

public import M9StacksIntegration.MukaiPencilDegreeBounds

/-!
# Degree bounds from the actual absence of a degree-seven net

An invertible sheaf with three genuine sections defines an actual net.
The native addition of an effective divisor raises its degree to seven,
so absence of such a net forces degree at least eight. The geometric
genus-nine proof of absence of a degree-seven net is a separate input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.MukaiNetFromNoSeven

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The original invertible sheaf has degree at least eight; the
linear series and degree padding are constructed natively. -/
theorem eight_le_degree_of_three_sections
    (hn : ¬ Nonempty (LinearSeries k f hdim 7 2)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h0 : 3 ≤ Module.finrank k (cohomologyOverField k f L 0)) :
    (8 : ℤ) ≤ invertibleCurveDegree k f hdim L := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank h0
  let s := MukaiSemiIrreducible.sectionOfH0 k f L (v 0)
  have hs : s.eval (op ⊤) ≠ 0 := by
    rw [MukaiSemiIrreducible.sectionOfH0_eval_top]
    intro hz
    apply hv.ne_zero 0
    have hh := congrArg (fun t => (cohomologyOverFieldZeroLinearIso k f L).inv t) hz
    simpa only [Iso.hom_inv_id_apply,map_zero] using hh
  have hnn := invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim L s hs
  let d := (invertibleCurveDegree k f hdim L).toNat
  have hd : invertibleCurveDegree k f hdim L = (d : ℤ) :=
    (Int.toNat_of_nonneg hnn).symm
  by_contra h
  have h7 : d ≤ 7 := by omega
  apply hn
  exact M9StacksIntegration.LinearSeriesAddEffectiveDivisor.nonempty_linearSeries_of_degree_le
    f hdim
    (LinearSeriesFromCohomology.nonempty_linearSeries_of_finrank_H0
      k f hdim L d 2 hd h0) h7

/-- Every original line of degree strictly below eight has at most two
sections when the actual curve has no degree-seven net. -/
theorem h0_le_two_of_degree_lt_eight
    (hn : ¬ Nonempty (LinearSeries k f hdim 7 2)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : invertibleCurveDegree k f hdim L < 8) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ Module.finrank k (cohomologyOverField k f L 0) := by omega
  exact (not_le_of_gt hdeg) (eight_le_degree_of_three_sections f hdim hn L h3)

end M9Native.MukaiNetFromNoSeven

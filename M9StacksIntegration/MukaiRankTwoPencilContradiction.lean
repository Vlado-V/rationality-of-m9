module

public import M9StacksIntegration.MukaiPencilDegreeBounds
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional

/-!
# Actual rank-two line-filtration contradictions

These use native short exact sequences and native degrees. Both outer
objects are actual invertible sheaves, with the two sections obtained
elsewhere from the actual exterior criterion and generated quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiRankTwoPencilContradiction

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

theorem degree_le_ten
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    {L E N : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    {i : L ⟶ E} {p : E ⟶ N} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact)
    (hE : curveDegree k f hdim E 2 ≤ 10)
    (hL : 2 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (hN : 2 ≤ Module.finrank k (cohomologyOverField k f N 0)) : False := by
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X N
  have hd := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk i p w) hS 1 2 1
  change curveDegree k f hdim E 2 = curveDegree k f hdim L 1 +
    curveDegree k f hdim N 1 at hd
  have hLd := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp L hL
  have hNd := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp N hN
  rw [invertibleCurveDegree_eq_curveDegree] at hLd hNd
  omega

theorem degree_twelve
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    {L E N : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    {i : L ⟶ E} {p : E ⟶ N} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact)
    (hE : curveDegree k f hdim E 2 = 12)
    (hL : 2 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (hN : 8 ≤ invertibleCurveDegree k f hdim N) : False := by
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X N
  have hd := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk i p w) hS 1 2 1
  change curveDegree k f hdim E 2 = curveDegree k f hdim L 1 +
    curveDegree k f hdim N 1 at hd
  have hLd := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp L hL
  rw [invertibleCurveDegree_eq_curveDegree] at hLd hN
  omega

end M9Native.MukaiRankTwoPencilContradiction

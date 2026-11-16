module

public import M9StacksIntegration.MukaiCanonicalTwistBounds

/-!
# Canonical section bounds from the actual residual Mukai nets

The residual isomorphism alpha tensor beta ≅ omega, with both actual
line bundles of degree eight, proves invertibility of omega and its
degree sixteen. Thus the canonical helpers require no separate
invertibility or canonical-degree premise in this genuine Mukai input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiResidualLineBounds

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The actual residual tensor isomorphism derives canonical invertibility. -/
theorem canonical_isInvertible (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (e : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Duality.dualizingSheafOverField f) := by
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (tensor alpha beta) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible
      X.presheaf X.ringCatSheaf.property alpha beta
  exact Stacks.SheafOfModules.isInvertible_of_iso X.presheaf X.ringCatSheaf.property e

variable (hdim : topologicalKrullDim X ≤ 1)

/-- The canonical degree is calculated from the original degree-eight residual nets. -/
theorem canonical_degree (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (e : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (ha : invertibleCurveDegree k f hdim alpha = 8)
    (hb : invertibleCurveDegree k f hdim beta = 8) :
    letI := canonical_isInvertible f alpha beta e
    invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) = 16 := by
  letI := canonical_isInvertible f alpha beta e
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (tensor alpha beta) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible
      X.presheaf X.ringCatSheaf.property alpha beta
  have hp := invertibleCurveDegree_tensorSheaf_eq_add k f hdim alpha beta
  change invertibleCurveDegree k f hdim (tensor alpha beta) =
    invertibleCurveDegree k f hdim alpha + invertibleCurveDegree k f hdim beta at hp
  have he := invertibleCurveDegree_eq_of_iso k f hdim e
  omega

/-- Degree at most ten allows at most four sections, from actual residual-net data. -/
theorem h0_le_four_of_degree_le_ten
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (e : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (ha : invertibleCurveDegree k f hdim alpha = 8)
    (hb : invertibleCurveDegree k f hdim beta = 8)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hd : invertibleCurveDegree k f hdim L ≤ 10) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 4 := by
  letI := canonical_isInvertible f alpha beta e
  have hω := canonical_degree f hdim alpha beta e ha hb
  have hC : invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) =
      2 * (genus f : ℤ) - 2 := by rw [hω, hg]; norm_num
  exact MukaiCanonicalTwistBounds.h0_le_four_of_degree_le_ten f hdim hC hg hnp L hd

/-- Degree twelve allows at most five sections, with the same actual residual data. -/
theorem h0_le_five_of_degree_twelve
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (e : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (ha : invertibleCurveDegree k f hdim alpha = 8)
    (hb : invertibleCurveDegree k f hdim beta = 8)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hd : invertibleCurveDegree k f hdim L = 12) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 5 := by
  letI := canonical_isInvertible f alpha beta e
  have hω := canonical_degree f hdim alpha beta e ha hb
  have hC : invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) =
      2 * (genus f : ℤ) - 2 := by rw [hω, hg]; norm_num
  exact MukaiCanonicalTwistBounds.h0_le_five_of_degree_twelve f hdim hC hg hnp L hd

end M9Native.MukaiResidualLineBounds

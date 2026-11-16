module

public import M9StacksIntegration.MukaiNoDegreeSevenNet
public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials

/-!
# Actual residual degrees from nonpentagonality and genuine sections

On a nonpentagonal genus-nine curve, an actual line with at least three
sections has degree at least eight. For two such actual lines whose
tensor product is the genuine canonical sheaf, the actual canonical
degree forces both degrees to be eight. Their complete H0 dimensions
are then three. No residual degree is assumed.

The original-system factory must separately construct the three
independent sections of each line; those geometric inputs are not
asserted by this numerical/cohomological lemma.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module
open M9Native.MukaiBundleDeterminant
universe u

namespace M9Native.MukaiNonpentagonalResidualDegrees

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
  (hdim : topologicalKrullDim X ≤ 1) (hg : genus f = 9)
  (hnp : ¬ Nonempty (LinearSeries K f hdim 5 1))

include hg hnp

/-- This is the contrapositive of the actual low-degree net obstruction. -/
theorem degree_ge_eight_of_three_sections (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : 3 ≤ finrank K (cohomologyOverField K f L 0)) :
    8 ≤ invertibleCurveDegree K f hdim L := by
  by_contra hn
  have hd : invertibleCurveDegree K f hdim L ≤ 7 := by omega
  have hb := MukaiNoDegreeSevenNet.h0_le_two_of_degree_le_seven f hdim hg hnp L hd
  omega

/-- The actual canonical tensor relation and genuine section counts
force both residual degrees, with no degree or canonical-degree premise. -/
theorem degrees_eight (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    (e : tensor A B ≅ Stacks.Duality.dualizingSheafOverField f)
    (hA : 3 ≤ finrank K (cohomologyOverField K f A 0))
    (hB : 3 ≤ finrank K (cohomologyOverField K f B 0)) :
    invertibleCurveDegree K f hdim A = 8 ∧ invertibleCurveDegree K f hdim B = 8 := by
  letI := isIso_globalSections_of_isAlgClosed K f
  letI := SmoothCurveCanonicalDifferentials.differentials_isInvertible f
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tensor A B) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible
      X.presheaf X.ringCatSheaf.2 A B
  have hA8 := degree_ge_eight_of_three_sections f hdim hg hnp A hA
  have hB8 := degree_ge_eight_of_three_sections f hdim hg hnp B hB
  have hp := invertibleCurveDegree_tensorSheaf_eq_add K f hdim A B
  change invertibleCurveDegree K f hdim (tensor A B) =
    invertibleCurveDegree K f hdim A + invertibleCurveDegree K f hdim B at hp
  have he := invertibleCurveDegree_eq_of_iso K f hdim
    (e ≪≫ SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso f)
  have hw := SmoothCurveCanonicalDifferentials.differentials_degree_genus_nine f hdim hg
  omega

/-- In the same actual residual geometry the complete section counts
are also conclusions, not supplied completeness assumptions. -/
theorem degrees_and_h0 (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    (e : tensor A B ≅ Stacks.Duality.dualizingSheafOverField f)
    (hA : 3 ≤ finrank K (cohomologyOverField K f A 0))
    (hB : 3 ≤ finrank K (cohomologyOverField K f B 0)) :
    invertibleCurveDegree K f hdim A = 8 ∧ invertibleCurveDegree K f hdim B = 8 ∧
      finrank K (cohomologyOverField K f A 0) = 3 ∧
      finrank K (cohomologyOverField K f B 0) = 3 := by
  obtain ⟨ha,hb⟩ := degrees_eight f hdim hg hnp A B e hA hB
  have hAc := MukaiNoDegreeSevenNet.h0_le_three_of_degree_le_eight f hdim hg hnp A ha.le
  have hBc := MukaiNoDegreeSevenNet.h0_le_three_of_degree_le_eight f hdim hg hnp B hb.le
  exact ⟨ha,hb,le_antisymm hAc hA,le_antisymm hBc hB⟩

end M9Native.MukaiNonpentagonalResidualDegrees

module

public import M9StacksIntegration.MukaiNoDegreeSevenNet
public import M9StacksIntegration.MukaiLengthTwoFiltration
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# Mukai Lemma 5.1 on the actual nonpentagonal genus-nine curve

The complete basis exists by the proved low-degree-net obstruction.
The length-two divisor and its two-section degree-six twist are produced
by the failed plane embedding. Minimal-degree generation supplies both
original evaluation epimorphisms; the actual dual evaluation diagram
then gives the actual divisor sequence. Native cohomology and degrees
give the two conclusions.

The accompanying audit records the source-bound kernel-check status.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace M9Native.MukaiLemmaFiveOne

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiDualSpanSections
open M9Native.CurveDivisorSections M9Native.CurveDivisorDegree
open Stacks.Divisors (IsEffectiveCartierDivisor)

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The original degree-eight net has an actual complete cohomology
basis; completeness is derived from the geometry of the original curve. -/
def completeNetBasis (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 8 2) :
    Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f E.L 0) := by
  let := E.isInvertible
  let := invertible_cohomology_zero_finite f E.L
  exact (Module.finBasisOfFinrankEq k (cohomologyOverField k f E.L 0)
    (MukaiNoDegreeSevenNet.degree_eight_net_h0_eq_three_and_complete f hdim hg hnp E).1).reindex
      Equiv.ulift.symm

/-- The two actual native-cohomology conclusions of Mukai Lemma 5.1,
for any chosen complete basis of the original degree-eight net. -/
theorem lemma_five_one_for_complete_basis (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 8 2)
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f E.L 0))
    (α : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (hα : invertibleCurveDegree k f hdim α = 8) :
    Module.finrank k (cohomologyOverField k f
      (dualSpan E.L (completeNetSections f E.L bβ)) 0) = 3 ∧
    Subsingleton (cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSheaf α) (dualSpan E.L (completeNetSections f E.L bβ))) 0) := by
  let := E.isInvertible
  let : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  have hno7 : ∀ d : ℕ, d ≤ 7 → ¬ Nonempty (LinearSeries k f hdim d 2) :=
    MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f hdim hg hnp
  obtain ⟨D, hDdim, hd, hfail⟩ :=
    MukaiNoDegreeSevenNet.exists_length_two_restriction_defect f hdim hg hnp E
  exact MukaiLengthTwoFiltration.count_and_vanishing_of_length_two_defect
    f hdim hnp hno7 E bβ D hDdim hd hfail α hα

/-- The same theorem with a basis actually constructed from the native
degree-eight net, leaving no complete-basis existence premise. -/
theorem lemma_five_one (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 8 2)
    (α : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (hα : invertibleCurveDegree k f hdim α = 8) :
    let bβ := completeNetBasis f hdim hg hnp E
    Module.finrank k (cohomologyOverField k f
      (dualSpan E.L (completeNetSections f E.L bβ)) 0) = 3 ∧
    Subsingleton (cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSheaf α) (dualSpan E.L (completeNetSections f E.L bβ))) 0) :=
  lemma_five_one_for_complete_basis f hdim hg hnp E (completeNetBasis f hdim hg hnp E) α hα

end M9Native.MukaiLemmaFiveOne

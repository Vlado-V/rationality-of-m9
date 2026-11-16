module

public import M9StacksIntegration.MukaiNoDegreeSevenNet
public import M9StacksIntegration.MukaiCompleteEvaluation
public import M9StacksIntegration.MukaiPencilQuotient

/-!
# The actual geometric inputs of Mukai's pencil quotient

The actual genus-nine/no-pentagonal-net argument constructs D and its
degree-six two-section twist. Minimal-degree generation supplies both
original evaluation epimorphisms for the chosen complete net basis.
This exports the genuine pencil data for use in tensoring the original
short exact sequence, without adding a divisor or generation premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace M9Native.MukaiPencilGeometry

open CategoryTheory AlgebraicGeometry
open MukaiBundle MukaiDualSpanSections CurveDivisorSections
open Stacks.Divisors (IsEffectiveCartierDivisor)

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- A genuine genus-nine degree-eight net produces the actual Cartier
divisor, complete pencil basis, and both original evaluation epis. -/
theorem exists_completePencilData (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 8 2)
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f E.L 0)) :
    ∃ (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D),
      topologicalKrullDim D.subscheme ≤ 0 ∧
      (letI : Algebra k Γ(D.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra;
        Module.finrank k Γ(D.subscheme, ⊤) = 2) ∧
      (letI := hD;
       letI := E.isInvertible;
       ∃ bξ : Module.Basis (ULift.{u} (Fin 2)) k
           (cohomologyOverField k f (twistDown D E.L) 0),
         invertibleCurveDegree k f hdim (twistDown D E.L) = 6 ∧
         Module.finrank k (cohomologyOverField k f (twistDown D E.L) 0) = 2 ∧
         Epi (MukaiPencilQuotient.pencilEvaluation (twistDown D E.L)
           (MukaiPencilQuotient.completePencilSections f D E.L bξ)) ∧
         Epi (netEvaluation E.L (completeNetSections f E.L bβ))) := by
  let := E.isInvertible
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f hdim hg hnp
  have heβ := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f hdim hno7 E bβ
  obtain ⟨D, hD, hDdim, hd, hξdegree, hξ0⟩ :=
    MukaiNoDegreeSevenNet.exists_length_two_degree_six_twist f hdim hg hnp E
  let := hD
  let ξ : X.Modules := twistDown D E.L
  let := invertible_cohomology_zero_finite f ξ
  let bξ : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f ξ 0) :=
    (Module.finBasisOfFinrankEq k (cohomologyOverField k f ξ 0) hξ0).reindex Equiv.ulift.symm
  let Eξ : LinearSeries k f hdim 6 1 :=
    { L := ξ
      isInvertible := inferInstance
      degree_eq := hξdegree
      V := ⊤
      finrank_eq := by simpa only [finrank_top] using hξ0 }
  have heξ : Epi (MukaiPencilQuotient.pencilEvaluation ξ
      (MukaiPencilQuotient.completePencilSections f D E.L bξ)) := by
    change Epi (CompleteEvaluationGeneration.basisEvaluation f ξ bξ)
    exact MukaiCompleteEvaluation.degree_six_completePencilEvaluation_epi f hdim hnp Eξ bξ
  exact ⟨D, hD, hDdim, hd, bξ, hξdegree, hξ0, heξ, heβ⟩

end M9Native.MukaiPencilGeometry

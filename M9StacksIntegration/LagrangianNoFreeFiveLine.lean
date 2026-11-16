module

public import M9StacksIntegration.MukaiRankTwoGeneratorSequence
public import M9StacksIntegration.MukaiPentagonalHomBound
public import M9StacksIntegration.LagrangianPentagonalImageHomZero
public import M9StacksIntegration.LagrangianFreeFiveAlphaHomZero

/-!
# The genuine free-five part of the original pentagonal contradiction

The original rank-two image has its true dual-determinant kernel
sequence. Native RR and Serre duality give an actual nonzero Hom in
one of the two original Hom spaces. The independent full-zero and
hyperplane-cokernel arguments exclude both possibilities.

Actual determinant degree eight remains an honest intermediate input.
The genuinely generating pair and actual complete H0 dimension two are
explicit. This does not assert the minimal free-four case or universal
nonpentagonality of good sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
universe u

namespace M9Native.LagrangianNoFreeFiveLine

open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles
open LagrangianFreeFiveResidualSections

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- Both proved Hom contradictions exclude a genuine free degree-five
line, using the true original rank-two image and its actual determinant. -/
theorem false_of_free_five_line
    (s : Fin 3 → (Fin 6 → K)) (hs : LinearIndependent K s)
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (hg : genus (modelProjection K M hM) = 9)
    (hno3 : ¬ Nonempty (LinearSeries K (modelProjection K M hM)
      (dimension_le_one K M hM) 3 1))
    (ξ : (model K M hM).Modules)
    [SheafOfModules.IsInvertible (model K M hM).presheaf (model K M hM).ringCatSheaf.2 ξ]
    (hβ : letI := beta_isInvertible K M hM s hr
      invertibleCurveDegree K (modelProjection K M hM) (dimension_le_one K M hM)
        (beta K M hM s) = 8)
    (hξ : invertibleCurveDegree K (modelProjection K M hM)
      (dimension_le_one K M hM) ξ = 5)
    (h2 : finrank K (cohomologyOverField K (modelProjection K M hM) ξ 0) = 2)
    (t : ULift.{u} (Fin 2) → ξ.sections)
    (ht : Epi (MukaiPencilQuotient.pencilEvaluation ξ t)) : False := by
  letI := model_isCurve K M hM
  letI := (ranks K M hM s hr).2.1
  letI := beta_isInvertible K M hM s hr
  let q : netFree (model K M hM) ⟶ imageBundle K M hM s :=
    factorThruImage (originalMap K M hM s)
  letI : Epi q := inferInstance
  obtain ⟨i,w,hS⟩ := MukaiRankTwoGeneratorSequence.exists_dualDeterminantSequence
    (imageBundle K M hM s) (beta K M hM s) q
    (LagrangianRankTwoSubsystemExistence.betaExteriorIso K M hM s hr).symm
  obtain ⟨g,hg0⟩ | ⟨g,hg0⟩ :=
    MukaiPentagonalHomBound.nonzero_hom_alternative_of_isAlgClosed
      (imageBundle K M hM s) (beta K M hM s) i q w hS K
      (modelProjection K M hM) hg (alpha K M hM s) ξ
      (betaTensorAlphaCanonicalIso K M hM s hr) hβ hξ h2
  · exact hg0 (LagrangianPentagonalImageHomZero.hom_eq_zero
      K M hM s hs hr ξ hβ hξ.le h2 g)
  · exact hg0 (LagrangianFreeFiveAlphaHomZero.hom_eq_zero
      K M hM s hs hr hg hno3 ξ hβ hξ h2 t ht g)

end M9Native.LagrangianNoFreeFiveLine

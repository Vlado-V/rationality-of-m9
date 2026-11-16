module

public import M9StacksIntegration.LagrangianTripleDeterminantSection
public import M9StacksIntegration.MukaiTripleDeterminantRank

/-!
# The genuine determinant alternative for the original six-section system

For every independent original triple on an actual regular integral
curve mapped to LG, either its original evaluation is sheaf-monic,
or its nonzero original primitive hyperplane restricts to zero and the
original evaluation has rank at most two on every actual residue fibre.
The five-row kernel and the transverse differential lower bound remain
separate geometric producers; no Semi or complete-H0 premise is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.LagrangianOriginalTripleAlternative

open LagrangianUniversalSections LagrangianUniversalTriples LagrangianTripleDeterminantSection

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) (l : X ⟶ LagrangianGrassmannian.space k)
  [IsIntegral X] (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)

include hreg hdim

/-- Nonmonicity of the original triple forces its actual original determinant to vanish. -/
theorem determinantValue_eq_zero_of_not_mono (s : Fin 3 → (Fin 6 → k))
    (hn : ¬ Mono (evaluation k f l s)) : determinantValue k f l s = 0 := by
  letI := bundle_rank k l
  exact MukaiTripleDeterminantRank.lambda_eq_zero_of_not_mono k f (bundle k l)
    hreg hdim (fun i => sectionMap k f l (s i)) hn

/-- The exact original primitive coefficient vector lies in the actual restriction kernel. -/
theorem primitiveRestriction_eq_zero_of_not_mono
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (s : Fin 3 → (Fin 6 → k))
    (hn : ¬ Mono (evaluation k f l s)) :
    LagrangianPrimitiveRestriction.primitiveRestriction k f l
      (PrimitiveDecomposableNonzero.coefficients k s) = 0 :=
  (determinantValue_eq_zero_iff k f l hl s).mp
    (determinantValue_eq_zero_of_not_mono k f l hreg hdim s hn)

/-- The determinant branch of the actual original quotient-system Semi argument. -/
theorem original_triple_alternative
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (s : Fin 3 → (Fin 6 → k))
    (hs : LinearIndependent k s) :
    Mono (evaluation k f l s) ∨
      (PrimitiveDecomposableNonzero.coefficients k s ≠ 0 ∧
        LagrangianPrimitiveRestriction.primitiveRestriction k f l
          (PrimitiveDecomposableNonzero.coefficients k s) = 0 ∧
        ∀ x : X, MukaiSemiIrreducible.mapRankAt (evaluation k f l s) x ≤ 2) := by
  classical
  letI := bundle_rank k l
  by_cases h : determinantValue k f l s = 0
  · refine Or.inr ⟨PrimitiveDecomposableNonzero.coefficients_ne_zero k s hs,
      (determinantValue_eq_zero_iff k f l hl s).mp h, ?_⟩
    intro x
    exact MukaiTripleDeterminantRank.mapRankAt_le_two_of_lambda_eq_zero k f (bundle k l)
      (fun i => sectionMap k f l (s i)) h x
  · exact Or.inl (MukaiTripleDeterminantRank.evaluation_mono_of_lambda_ne_zero
      k f (bundle k l) hreg hdim (fun i => sectionMap k f l (s i)) h)

end M9Native.LagrangianOriginalTripleAlternative

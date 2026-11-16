module

public import M9StacksIntegration.LagrangianIncidenceBetaTransfer
public import M9StacksIntegration.LagrangianIncidenceFourCutEight

/-! The actual beta divisor on the original curve has length eight.
The complete incidence/four-cut/C-only comparison derives finiteness,
the genuine incidence class and LG degree derive the value, and the
actual subsystem producer removes all chosen-pair inputs at the final
existence endpoint. This source is staged until all actual geometric
producers have checked objects; no desired length is a premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
universe u
namespace M9Native.LagrangianIncidenceBetaEight
open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles LagrangianBetaRankDrop
open LagrangianIncidenceBetaTransfer LagrangianBetaCurveDegree

variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

theorem nativeBetaZeroLength_eq_eight (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) (hw : LinearIndependent K (s ∘ e))
    (hs : betaSection K M hM s hr e ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    nativeBetaZeroLength K M hM s hr e = 8 := by
  letI := fourCut_isFinite K M hM s hr e hs A hfirst
  have htransport := finrank_fourCut_eq_nativeBetaZeroLength K M hM s hr e A hfirst
  have hlength := LagrangianIncidenceFourCutEight.finrank_fourCut_eq_eight_nat
    K (s ∘ e) hw (A.val * M)
  exact htransport.symm.trans hlength

variable [IsAlgClosed K]

/-- The original smooth integral curve itself produces the actual
pair and its nonzero beta section with FULL native zero length eight.
No pair, isomorphism, finiteness, class or numerical value is supplied. -/
theorem exists_actual_pair_length_eight :
    ∃ (s : Fin 3 → (Fin 6 → K))
      (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
      (e : Fin 2 ↪ Fin 3) (A : Matrix.GeneralLinearGroup (Fin 5) K),
      LinearIndependent K s ∧ LinearIndependent K (s ∘ e) ∧
      betaSection K M hM s hr e ≠ 0 ∧
      (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s ∧
      nativeBetaZeroLength K M hM s hr e = 8 := by
  obtain ⟨s, hr, e, A, hs, hw, hbeta, _hAM, hfirst, _hnonzero, _hiso, _hfinite⟩ :=
    LagrangianBetaFourCut.exists_finite_fourCut K M hM
  exact ⟨s, hr, e, A, hs, hw, hbeta, hfirst,
    nativeBetaZeroLength_eq_eight K M hM s hr e hw hbeta A hfirst⟩

end M9Native.LagrangianIncidenceBetaEight

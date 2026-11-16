module

public import M9StacksIntegration.LagrangianIncidenceFourCut
public import M9StacksIntegration.LagrangianIncidenceFourCapPush
public import M9StacksIntegration.LagrangianSelectedPairIncidenceIso
public import M9StacksIntegration.LagrangianBetaCurveDegree

/-! Actual original-curve transfer for the FULL four-cut on incidence.
The genuine C-only incidence comparison is composed with the actual
changed-equation/kernel pullback comparison. Finiteness and the
original-field global-function dimension then follow from the nonzero
actual beta section. No global incidence/rank-drop isomorphism,
finite-length value, supplied scheme isomorphism or scalar-ID premise
is introduced.

This source is staged until the separately owned original C-only
incidence comparison is kernel-checked. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
namespace M9Native.LagrangianIncidenceBetaTransfer
open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles LagrangianBetaRankDrop
open LagrangianIncidenceFourCutBase LagrangianIncidenceFourCut
open LagrangianIncidenceFourCapPush LagrangianBetaCurveDegree

variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

def fourIsoNativeBetaZero (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    fourCut K (s ∘ e) (A.val * M) ≅
      (nativeBetaZeroIdeal K M hM s hr e).subscheme :=
  fourIsoCurvePullback K M hM s e A hfirst ≪≫
    LagrangianSelectedPairIncidenceIso.curveIncidenceIsoBeta K M hM s hr e

@[reassoc] theorem fourIsoNativeBetaZero_hom_toLG (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (fourIsoNativeBetaZero K M hM s hr e A hfirst).hom ≫
      (nativeBetaZeroIdeal K M hM s hr e).subschemeι ≫ modelInclusion K M hM =
        fourInclusion K (s ∘ e) (A.val * M) ≫
          LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e) := by
  have h := congrArg
    (fun a => (fourIsoCurvePullback K M hM s e A hfirst).hom ≫ a ≫ modelInclusion K M hM)
    (LagrangianSelectedPairIncidenceIso.curveIncidenceIsoBeta_hom_fst K M hM s hr e)
  have hcomp : (fourIsoNativeBetaZero K M hM s hr e A hfirst).hom ≫
      (nativeBetaZeroIdeal K M hM s hr e).subschemeι ≫ modelInclusion K M hM =
      (fourIsoCurvePullback K M hM s e A hfirst).hom ≫ pullback.fst _ _ ≫
        modelInclusion K M hM := by
    simpa only [fourIsoNativeBetaZero, Iso.trans_hom, Category.assoc] using h
  exact hcomp.trans (fourIsoCurvePullback_hom_toLG K M hM s e A hfirst)

@[reassoc] theorem fourIsoNativeBetaZero_over (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (fourIsoNativeBetaZero K M hM s hr e A hfirst).hom ≫
      nativeBetaZeroProjection K M hM s hr e =
        fourInclusion K (s ∘ e) (A.val * M) ≫ structuralMap K (s ∘ e) := by
  simpa only [nativeBetaZeroProjection, modelProjection, structuralMap, Category.assoc] using
    congrArg (fun a => a ≫ LagrangianGrassmannian.projection K)
      (fourIsoNativeBetaZero_hom_toLG K M hM s hr e A hfirst)

/-- Actual finiteness of the FULL original incidence four-cut follows
from the actual nonzero beta section on the original curve. -/
theorem fourCut_isFinite (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) (hs : betaSection K M hM s hr e ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    IsFinite (fourInclusion K (s ∘ e) (A.val * M) ≫ structuralMap K (s ∘ e)) := by
  letI := nativeBetaZero_finite K M hM s hr e hs
  rw [← fourIsoNativeBetaZero_over K M hM s hr e A hfirst]
  infer_instance

/-- Both sides use the original structural K-algebra on global
functions, retaining all nilpotents. The structural triangle is proved. -/
theorem finrank_fourCut_eq_nativeBetaZeroLength (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
    (e : Fin 2 ↪ Fin 3) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    letI : Algebra K Γ(fourCut K (s ∘ e) (A.val * M), ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        (fourInclusion K (s ∘ e) (A.val * M) ≫ structuralMap K (s ∘ e)).appTop).hom.toAlgebra
    finrank K Γ(fourCut K (s ∘ e) (A.val * M), ⊤) =
      nativeBetaZeroLength K M hM s hr e :=
  SchemeGlobalSectionsIso.finrank_globalSections_eq K
    (fourInclusion K (s ∘ e) (A.val * M) ≫ structuralMap K (s ∘ e))
    (nativeBetaZeroProjection K M hM s hr e)
    (fourIsoNativeBetaZero K M hM s hr e A hfirst)
    (fourIsoNativeBetaZero_over K M hM s hr e A hfirst)

end M9Native.LagrangianIncidenceBetaTransfer

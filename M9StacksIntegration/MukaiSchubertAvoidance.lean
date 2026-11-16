module

public import M9StacksIntegration.MukaiSemiExclusions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Actual exterior-evaluation kernel avoids the rank-one Schubert locus

For an actual independent triple in the kernel of the third exterior
evaluation, native semi-irreducibility forces evaluation rank exactly two
on every actual residue fiber. Thus no decomposable kernel vector comes
from a triple whose evaluation at a prescribed point has rank at most
one. This derives the geometric avoidance condition from actual Semi3.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module TopologicalSpace

namespace M9Native.MukaiSchubertAvoidance

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The actual top wedge of an independent triple in a three-dimensional
space is nonzero, verified by the dual basis determinant. -/
theorem wedge_three_ne_zero (hV : Module.finrank K V = 3)
    (s : Fin 3 → V) (hs : LinearIndependent K s) :
    exteriorPower.ιMulti K 3 s ≠ 0 := by
  let b : Basis (Fin 3) K V := basisOfLinearIndependentOfCardEqFinrank hs (by simpa using hV.symm)
  have hb : ∀ i, b i = s i := fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hs _) i
  let φ := exteriorPower.pairingDual K V 3
    (exteriorPower.ιMulti K 3 (fun i => b.coord i))
  have hφ : φ (exteriorPower.ιMulti K 3 s) = 1 := by
    dsimp only [φ]
    rw [exteriorPower.pairingDual_ιMulti_ιMulti]
    have hm : Matrix.of (fun i j => b.coord j (s i)) = (1 : Matrix (Fin 3) (Fin 3) K) := by
      funext i j
      simp only [Matrix.of_apply]
      rw [← hb i]
      simp [Matrix.one_apply, Finsupp.single_apply]
    rw [hm, Matrix.det_one]
  intro hz
  have h := congrArg φ hz
  rw [hφ, map_zero] at h
  exact one_ne_zero h

/-- Vanishing of the actual third wedge bounds the actual tuple span. -/
theorem finrank_span_le_two_of_wedge_eq_zero (hV : Module.finrank K V = 3)
    (s : Fin 3 → V) (hs : exteriorPower.ιMulti K 3 s = 0) :
    Module.finrank K (Submodule.span K (Set.range s)) ≤ 2 := by
  by_contra hn
  have hr : 3 ≤ Module.finrank K (Submodule.span K (Set.range s)) := by omega
  have hi : LinearIndependent K s :=
    linearIndependent_iff_card_le_finrank_span.mpr (by
      simpa only [Fintype.card_fin, Set.finrank] using hr)
  exact wedge_three_ne_zero hV s hi hs

end Linear

universe u

variable {X : Scheme.{u}} [IsIntegral X] (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

omit [IsIntegral X] in
/-- Actual exterior-evaluation vanishing gives actual rank at most two
at every residue point, with no generic-rank hypothesis. -/
theorem mapRankAt_le_two_of_lambda_three_eq_zero
    (s : Fin 3 → cohomologyOverField k f E 0)
    (hs : ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 s) = 0)
    (x : X) :
    MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E s) x ≤ 2 := by
  let := TupleEvaluationFiber.residueAlgebra x
  let := TupleEvaluationFiber.fiberFinite E 3 x
  rw [MukaiSemiExclusions.mapRankAt_eq_finrank_valueSpan]
  apply finrank_span_le_two_of_wedge_eq_zero (TupleEvaluationFiber.finrank_fiber E 3 x)
  exact ExteriorEvaluation.wedge_fiber_eq_zero_of_lambda_eq_zero k f x
    (X.residueField x) E 3 s hs

/-- Actual Semi3 derives rank exactly two in every fiber for each
independent triple in the original third-exterior kernel. -/
theorem everywhereRank_two_of_kernel
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (s : Fin 3 → cohomologyOverField k f E 0) (hlin : LinearIndependent k s)
    (hs : ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 s) = 0) :
    MukaiSemiIrreducible.EverywhereRank (MukaiSemiIrreducible.evaluation k f E s) 2 := by
  rcases hsemi s hlin with hmono | hrank
  · let := hmono
    have hr := MukaiSemiExclusions.mapRankAt_generic_of_mono k f E s
    have hb := mapRankAt_le_two_of_lambda_three_eq_zero k f E s hs (genericPoint X)
    omega
  · exact hrank

/-- The ORIGINAL exterior kernel avoids the actual rank-one Schubert
condition at every point; cone avoidance is not a premise. -/
theorem lambda_three_ne_zero_of_rankAt_le_one
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (s : Fin 3 → cohomologyOverField k f E 0) (hlin : LinearIndependent k s)
    (x : X) (hx : MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation k f E s) x ≤ 1) :
    ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 s) ≠ 0 := by
  intro hz
  have h := everywhereRank_two_of_kernel k f E hsemi s hlin hz x
  omega

end M9Native.MukaiSchubertAvoidance

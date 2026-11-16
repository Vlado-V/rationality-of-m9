module

public import M9StacksIntegration.MukaiSchubertCone
public import M9StacksIntegration.MukaiSchubertAvoidance
public import M9StacksIntegration.MukaiPrimitiveCanonicalEvaluation

/-!
# Actual cubic-cone avoidance at a normalized closed point

The point hypothesis is the explicit coordinate formula for the ORIGINAL
closed-point evaluation in an actual complete H0 basis. Semi3 then
excludes the actual decomposable Schubert vectors constructed from every
singular ternary matrix. Neither discriminant avoidance nor a kernel
line is supplied to the result.

The native I/I²/first-jet comparison and the existence of this coordinate
normalization are separate geometric steps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.MukaiConormalClosedPoint

open LagrangianField MukaiConormalPrimitive MukaiPrimitiveCanonicalEvaluation

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) (E : X.Modules)
    (b : Basis (Fin 6) k (cohomologyOverField k f E 0))

set_option backward.isDefEq.respectTransparency true in
theorem primitiveEvaluation_primitiveClass
    (hσ : ExteriorEvaluation.lambda k f E 2 (MukaiLagrangianMap.basisSigma k f E b) = 0)
    (w : Third k) :
    primitiveEvaluation k f E b (primitiveClass k w) = lambdaThree k f E b w := by
  change primitiveEvaluation k f E b
    (MukaiPrimitiveDuality.restriction k (MukaiPrimitiveDuality.coefficientDuality k w)) = _
  rw [primitiveEvaluation_restriction k f E b hσ, LinearEquiv.symm_apply_apply]

variable [IsAlgClosed k] [IsIntegral X] [LocallyOfFiniteType f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

theorem discriminant_ne_zero_of_kernel
    (hσ : ExteriorEvaluation.lambda k f E 2 (MukaiLagrangianMap.basisSigma k f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hnorm : ∀ v : V k, MukaiSemiExclusions.closedEvaluation k f E x hx
      (b.equivFun.symm v) = MukaiSchubertCone.firstProjection k v)
    (v : MukaiConormalPencil.ConormalCoordinates k) (hv : v ≠ 0)
    (hker : primitiveEvaluation k f E b (conormalForm k v) = 0) :
    MukaiConormalPencil.discriminant v ≠ 0 := by
  intro hdet
  obtain ⟨s,hlin,he,hrank⟩ := MukaiSchubertCone.exists_independent_triple_of_discriminant_zero
    k v hv hdet
  let t : Fin 3 → cohomologyOverField k f E 0 := fun i => b.equivFun.symm (s i)
  have hlin' : LinearIndependent k t :=
    hlin.map' b.equivFun.symm.toLinearMap (LinearMap.ker_eq_bot.mpr b.equivFun.symm.injective)
  have hWedge : ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 t) = 0 := by
    rw [← lambdaThree_ιMulti k f E b s, ← primitiveEvaluation_primitiveClass k f E b hσ, he]
    exact hker
  have hbad : MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation k f E t) x ≤ 1 := by
    rw [MukaiSemiExclusions.closedEvaluation_rank k f E x hx]
    change Module.finrank k (Submodule.span k (Set.range (fun i =>
      MukaiSemiExclusions.closedEvaluation k f E x hx (b.equivFun.symm (s i))))) ≤ 1
    have heval : (fun i => MukaiSemiExclusions.closedEvaluation k f E x hx
        (b.equivFun.symm (s i))) = (fun i => MukaiSchubertCone.firstProjection k (s i)) :=
      funext fun i => hnorm (s i)
    rw [heval]
    exact hrank
  exact MukaiSchubertAvoidance.lambda_three_ne_zero_of_rankAt_le_one
    k f E hsemi t hlin' x hbad hWedge

def originIntersection : Submodule k (MukaiConormalPencil.ConormalCoordinates k) :=
  LinearMap.ker ((primitiveEvaluation k f E b).comp (conormalForm k))

theorem finrank_originIntersection_le_one
    (hσ : ExteriorEvaluation.lambda k f E 2 (MukaiLagrangianMap.basisSigma k f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hnorm : ∀ v : V k, MukaiSemiExclusions.closedEvaluation k f E x hx
      (b.equivFun.symm v) = MukaiSchubertCone.firstProjection k v) :
    Module.finrank k (originIntersection k f E b) ≤ 1 := by
  apply MukaiConormalPencil.finrank_le_one_of_det_ne_zero
    (originIntersection k f E b) MukaiConormalPencil.matrixProjection
  intro v hv hne
  exact discriminant_ne_zero_of_kernel k f E b hσ hsemi x hx hnorm v hne hv

end M9Native.MukaiConormalClosedPoint

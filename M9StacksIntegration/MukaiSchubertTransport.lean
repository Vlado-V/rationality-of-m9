module

public import M9StacksIntegration.MukaiSchubertCone
public import M9StacksIntegration.MukaiQuarticGradientTransport
public import M9StacksIntegration.LagrangianSymplecticAction

/-! The genuine decomposable Schubert witnesses are transported by the
original six-dimensional symplectic matrix. Their actual quotient rank
is retained, together with the exact original primitive coefficient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiSchubertTransport

open LagrangianField LagrangianTransitivity LagrangianSymplecticAction
open LagrangianSigmaInvariance
open MukaiConormalPrimitive MukaiPrimitiveQuartic MukaiPrimitiveQuarticAction
open MukaiPrimitiveSymplectic MukaiQuarticGradientTransport

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
theorem matrixSix_mul_inverse (g : Matrix.symplecticGroup (Fin 3) K) (v : V K) :
    (matrixSix K g).mulVec ((matrixSix K g⁻¹).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← matrixSix_mul, mul_inv_cancel, matrixSix_one, Matrix.one_mulVec]

variable [IsAlgClosed K]

/-- No cone or decomposability premise is supplied: a singular
transformed conormal form produces a true independent triple in the
original six-space, with true rank at most one for [I|0]g. -/
theorem exists_independent_triple_of_discriminant_zero
    (g : Matrix.symplecticGroup (Fin 3) K)
    (v : MukaiConormalPencil.ConormalCoordinates K) (hv : v ≠ 0)
    (hdet : v.2.val.det = 0) :
    ∃ s : Fin 3 → V K, LinearIndependent K s ∧
      primitiveClass K (exteriorPower.ιMulti K 3 s) =
        formsAction K g⁻¹ (conormalForm K v) ∧
      finrank K (Submodule.span K (Set.range (fun i =>
        MukaiSchubertCone.firstProjection K ((matrixSix K g).mulVec (s i))))) ≤ 1 := by
  obtain ⟨t,ht,he,hr⟩ := MukaiSchubertCone.exists_independent_triple_of_discriminant_zero
    K v hv hdet
  let s : Fin 3 → V K := fun i => symplecticEquiv K g⁻¹ (t i)
  have hs : LinearIndependent K s := ht.map' (symplecticEquiv K g⁻¹).toLinearMap
    (LinearMap.ker_eq_bot.mpr (symplecticEquiv K g⁻¹).injective)
  refine ⟨s,hs,?_,?_⟩
  · have hσ := symplecticEquiv_preserves_sigma K g⁻¹
    rw [symplecticEquiv_toLinearMap] at hσ
    have h := quotientMap_primitiveClass K (matrixSix K g⁻¹).mulVecLin hσ
      (exteriorPower.ιMulti K 3 t)
    rw [he, exteriorPower.map_apply_ιMulti, quotientMap_eq_dualMap_transpose] at h
    exact h.symm
  · have hst : (fun i => MukaiSchubertCone.firstProjection K
        ((matrixSix K g).mulVec (s i))) =
        (fun i => MukaiSchubertCone.firstProjection K (t i)) := by
      funext i
      change MukaiSchubertCone.firstProjection K
        ((matrixSix K g).mulVec ((matrixSix K g⁻¹).mulVec (t i))) = _
      rw [matrixSix_mul_inverse]
    rw [hst]
    exact hr

end M9Native.MukaiSchubertTransport

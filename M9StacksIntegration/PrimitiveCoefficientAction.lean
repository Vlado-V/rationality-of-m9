module

public import M9StacksIntegration.PrimitiveRingRepresentation
public import M9StacksIntegration.LagrangianSigmaInvariance
public import M9StacksIntegration.ExteriorCoefficientTranspose

/-!
# The actual primitive action and coefficient-dual transpose

The primitive subspace is the actual kernel of symplectic contraction.
Restriction of the literal exterior coefficient duality intertwines a
symplectic matrix with the dual primitive action of its transpose.  The
alternating primitive pairing is not substituted for this dot-duality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

universe u

namespace M9Native.PrimitiveCoefficientAction

open LagrangianTransitivity MukaiPrimitiveDuality

variable (k : Type u) [Field k]

/-- Literal identity on the actual exterior vectors compares the native
ring and native field contraction kernels. -/
def primitiveEquiv : PrimitiveRingRepresentation.Primitive k ≃ₗ[k] LagrangianField.Primitive k where
  toFun w := ⟨w.val, by
    change LagrangianField.contraction k w.val = 0
    rw [← LagrangianRing.contraction_eq_field]
    exact w.property⟩
  invFun w := ⟨w.val, by
    change LagrangianRing.contraction k w.val = 0
    rw [LagrangianRing.contraction_eq_field]
    exact w.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual native symplectic action on the actual primitive kernel. -/
def primitiveAction (g : Matrix.symplecticGroup (Fin 3) k) :
    LagrangianField.Primitive k ≃ₗ[k] LagrangianField.Primitive k :=
  (primitiveEquiv k).symm.trans
    ((PrimitiveRingRepresentation.primitiveLinear k g).trans (primitiveEquiv k))

theorem primitiveAction_val (g : Matrix.symplecticGroup (Fin 3) k)
    (v : LagrangianField.Primitive k) :
    (primitiveAction k g v).val = exteriorPower.map 3 (matrixSix k g).mulVecLin v.val := rfl

section DualRestriction

variable [CharZero k]

omit [CharZero k] in
/-- Restriction respects the actual transpose action on the original
coefficient-dual module of native primitive projective coordinates. -/
theorem restriction_transpose (g : Matrix.symplecticGroup (Fin 3) k) (w : LagrangianField.Third k) :
    restriction k (coefficientDuality k (exteriorPower.map 3 (matrixSix k g).mulVecLin w)) =
      (primitiveAction k (LagrangianSigmaInvariance.transposeSymplectic k g)).dualMap
        (restriction k (coefficientDuality k w)) := by
  apply LinearMap.ext
  intro v
  change coefficientDuality k (exteriorPower.map 3 (matrixSix k g).mulVecLin w) v.val =
    coefficientDuality k w (primitiveAction k (LagrangianSigmaInvariance.transposeSymplectic k g) v).val
  rw [primitiveAction_val, LagrangianSigmaInvariance.matrixSix_transpose]
  exact ExteriorCoefficientTranspose.coefficientDuality_exteriorPower_transpose k (matrixSix k g) w v.val

theorem restriction_extension (ell : Module.Dual k (LagrangianField.Primitive k)) :
    restriction k (extension k ell) = ell := by
  apply LinearMap.ext
  intro v
  change ell (primitiveProjection k v.val) = ell v
  congr 1
  change LagrangianField.primitiveEquiv k (LagrangianField.coordinateProjection k v.val) = v
  rw [← LagrangianField.primitiveEquiv_symm, LinearEquiv.apply_symm_apply]

section FactoredEvaluation

variable {W : Type u} [AddCommGroup W] [Module k W]

/-- The factored exterior evaluation has the actual contragredient
primitive action, obtained from restriction rather than a dimension identification. -/
theorem factor_restriction_transpose (L : LagrangianField.Third k →ₗ[k] W)
    (hL : ∀ v, L (wedgeSigma k v) = 0)
    (g : Matrix.symplecticGroup (Fin 3) k) (w : LagrangianField.Third k) :
    factor k L ((primitiveAction k (LagrangianSigmaInvariance.transposeSymplectic k g)).dualMap
      (restriction k (coefficientDuality k w))) =
      L (exteriorPower.map 3 (matrixSix k g).mulVecLin w) := by
  rw [← restriction_transpose, factor_restriction k L hL, LinearEquiv.symm_apply_apply]

end FactoredEvaluation

end DualRestriction

section ExteriorScalars

variable {E F : Type u} [AddCommGroup E] [Module k E] [AddCommGroup F] [Module k F]

/-- Scaling an actual linear map scales its true n-th exterior power by
the n-th power of the scalar. -/
theorem exteriorPower_map_smul (n : ℕ) (t : k) (f : E →ₗ[k] F) :
    exteriorPower.map n (t • f) = t ^ n • exteriorPower.map n f := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.map n (t • f) (exteriorPower.ιMulti k n v) =
    t ^ n • exteriorPower.map n f (exteriorPower.ιMulti k n v)
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
  change exteriorPower.ιMulti k n (fun i => t • f (v i)) = _
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Function.comp_def] using
    (exteriorPower.ιMulti k n).map_smul_univ (fun _ : Fin n => t) (fun i => f (v i))

end ExteriorScalars

theorem mulVecLin_smul (t : k) (A : Matrix (Fin 6) (Fin 6) k) :
    (t • A).mulVecLin = t • A.mulVecLin := by
  apply LinearMap.ext
  intro v
  exact Matrix.smul_mulVec t A v

end M9Native.PrimitiveCoefficientAction

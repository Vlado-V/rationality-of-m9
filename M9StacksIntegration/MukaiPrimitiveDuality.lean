module

public import M9StacksIntegration.LagrangianPluckerFactor

/-!
# The dual primitive quotient for exterior evaluation

The quotient coordinate module of the native primitive projective space is
`Dual (ker contraction)`.  This file uses the actual exterior coefficient
pairing to identify the kernel of restriction with the image of `sigma ∧ -`.
The resulting factorization uses the checked twenty/fourteen decomposition;
no identification of the primitive kernel with that quotient is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open Module
open scoped BigOperators

universe u

namespace M9Native.MukaiPrimitiveDuality

open LagrangianField

variable (k : Type u) [Field k]

/-- Exterior coefficients use the literal exterior basis underlying the
native Plucker coordinates. -/
def coefficientDuality : Third k ≃ₗ[k] Module.Dual k (Third k) :=
  (thirdBasis20 k).toDualEquiv

def vectorDuality : V k ≃ₗ[k] Module.Dual k (V k) :=
  (Pi.basisFun k (Fin 6)).toDualEquiv

/-- The actual linear map `v ↦ sigma ∧ v`, with the standard bivector in
the first-three/last-three order of the native LG. -/
def wedgeSigma : V k →ₗ[k] Third k :=
  ∑ i : Fin 3, (exteriorPower.ιMulti k 3).toMultilinearMap.toLinearMap
    ![e k i, f k i, 0] (2 : Fin 3)

theorem wedgeSigma_apply (v : V k) :
    wedgeSigma k v = ∑ i : Fin 3, wedge3 k (e k i) (f k i) v := by
  simp only [wedgeSigma, LinearMap.sum_apply, MultilinearMap.toLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  change exteriorPower.ιMulti k 3 (Function.update ![e k i, f k i, 0] (2 : Fin 3) v) =
    exteriorPower.ιMulti k 3 ![e k i, f k i, v]
  apply congrArg (exteriorPower.ιMulti k 3)
  funext j
  fin_cases j <;> rfl

theorem vectorDuality_apply (v w : V k) :
    vectorDuality k v w = ∑ i : Fin 6, v i * w i := by
  calc
    _ = vectorDuality k v (∑ i : Fin 6, w i • Pi.basisFun k (Fin 6) i) := by
      congr 1
      exact ((Pi.basisFun k (Fin 6)).sum_repr w).symm
    _ = ∑ i : Fin 6, w i * v i := by
      simp only [map_sum, map_smul, vectorDuality, Basis.toDualEquiv_apply,
        Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

/-- The adjoint identity is checked on actual coordinate wedges; repeated
indices are allowed, so this is independent of any enumeration of the
twenty increasing triples. -/
theorem wedgeSigma_coordinate (a b c : Fin 6) (v : V k) :
    exteriorPower.pairingDual k (V k) 3
      (exteriorPower.ιMulti k 3 ![LinearMap.proj a, LinearMap.proj b, LinearMap.proj c])
      (wedgeSigma k v) =
    vectorDuality k v (contraction k
      (wedge3 k (basisVector k a) (basisVector k b) (basisVector k c))) := by
  have hv (j : Fin 6) : vectorDuality k v (basisVector k j) = v j := by
    simpa [vectorDuality, basisVector] using
      (Pi.basisFun k (Fin 6)).toDual_apply_left v j
  rw [wedgeSigma_apply, map_sum, contraction_wedge3]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hv]
  simp only [wedge3, exteriorPower.pairingDual_ιMulti_ιMulti]
  simp only [Matrix.det_fin_three, LinearMap.proj_apply, basisVector, e, f, eIndex, fIndex,
    omega_apply, omegaValue, Fin.sum_univ_succ, Pi.single_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [show ∀ i j : Fin 6, (i = j) = (j = i) from fun i j => propext eq_comm]
  ring

/-- Contraction and multiplication by the actual standard bivector are
adjoints under the coefficient pairings. -/
theorem contraction_dual_wedgeSigma (v : V k) :
    coefficientDuality k (wedgeSigma k v) =
      (contraction k).dualMap (vectorDuality k v) := by
  apply (thirdBasis20 k).ext
  intro j
  rw [coefficientDuality, Basis.toDualEquiv_apply, Basis.toDual_apply_left]
  change (thirdBasis20 k).coord j (wedgeSigma k v) = _
  rw [← LagrangianPluckerLinear.coordinate3_triple]
  change coordinate3 k (LagrangianRing.triple j) (wedgeSigma k v) =
    vectorDuality k v (contraction k (thirdBasis20 k j))
  rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply]
  have h₁ : (fun i : Fin 3 => (LinearMap.proj (LagrangianRing.triple j i) : V k →ₗ[k] k)) =
      ![LinearMap.proj (LagrangianRing.triple j 0),
        LinearMap.proj (LagrangianRing.triple j 1),
        LinearMap.proj (LagrangianRing.triple j 2)] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : (fun i => LagrangianRing.basisVector k (LagrangianRing.triple j i)) =
      ![basisVector k (LagrangianRing.triple j 0),
        basisVector k (LagrangianRing.triple j 1),
        basisVector k (LagrangianRing.triple j 2)] := by
    funext i
    fin_cases i <;> rfl
  simp only [coordinate3, h₁, h₂]
  exact wedgeSigma_coordinate k (LagrangianRing.triple j 0)
    (LagrangianRing.triple j 1) (LagrangianRing.triple j 2) v

theorem coefficientSharp_contraction_dual (ell : Module.Dual k (V k)) :
    (coefficientDuality k).symm ((contraction k).dualMap ell) =
      wedgeSigma k ((vectorDuality k).symm ell) := by
  apply (coefficientDuality k).injective
  rw [LinearEquiv.apply_symm_apply, contraction_dual_wedgeSigma,
    LinearEquiv.apply_symm_apply]

/-- A native determinant coordinate is sent to the corresponding actual
coordinate wedge, including its order and sign. -/
theorem coefficientSharp_coordinate (c : Fin 3 ↪ Fin 6) :
    (coefficientDuality k).symm (coordinate3 k c) =
      exteriorPower.ιMulti k 3 (fun i => basisVector k (c i)) := by
  apply (coefficientDuality k).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (thirdBasis20 k).ext
  intro j
  rw [coefficientDuality, Basis.toDualEquiv_apply, Basis.toDual_apply_left]
  change coordinate3 k c (thirdBasis20 k j) =
    (thirdBasis20 k).coord j (exteriorPower.ιMulti k 3 (fun i => basisVector k (c i)))
  rw [← LagrangianPluckerLinear.coordinate3_triple]
  rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply]
  simp only [coordinate3, exteriorPower.pairingDual_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext a b
  simp [basisVector, LagrangianRing.basisVector, Pi.single_apply, eq_comm]

variable [CharZero k]

/-- The retraction onto the literal primitive kernel, with its actual
inclusion equal to the checked fourteen-coordinate projection. -/
def primitiveProjection : Third k →ₗ[k] Primitive k :=
  (primitiveEquiv k).toLinearMap.comp (coordinateProjection k)

theorem primitiveProjection_subtype :
    (Primitive k).subtype.comp (primitiveProjection k) =
      (coordinateEmbedding k).comp (coordinateProjection k) := by
  apply LinearMap.ext
  intro w
  exact primitiveEquiv_val k _

def restriction : Module.Dual k (Third k) →ₗ[k] Module.Dual k (Primitive k) :=
  (Primitive k).subtype.dualMap

def extension : Module.Dual k (Primitive k) →ₗ[k] Module.Dual k (Third k) :=
  (primitiveProjection k).dualMap

theorem dual_decomposition (ell : Module.Dual k (Third k)) :
    extension k (restriction k ell) +
      (contraction k).dualMap ((correction k).dualMap ell) = ell := by
  apply LinearMap.ext
  intro w
  change ell ((Primitive k).subtype (primitiveProjection k w)) +
    ell (correction k (contraction k w)) = ell w
  rw [← map_add]
  congr 1
  have h := LinearMap.congr_fun (primitive_linear_decomposition k) w
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    ← primitiveProjection_subtype] using h

section Factor
variable {T : Type*} [AddCommGroup T] [Module k T]

/-- An actual map annihilating `sigma ∧ V` descends to the native primitive
coordinate module.  Its input is the dual primitive module, as required by
the native projective convention. -/
def factor (L : Third k →ₗ[k] T) : Module.Dual k (Primitive k) →ₗ[k] T :=
  L.comp ((coefficientDuality k).symm.toLinearMap.comp (extension k))

theorem factor_restriction (L : Third k →ₗ[k] T)
    (hL : ∀ v, L (wedgeSigma k v) = 0) (ell : Module.Dual k (Third k)) :
    factor k L (restriction k ell) = L ((coefficientDuality k).symm ell) := by
  have h := congrArg (fun z => L ((coefficientDuality k).symm z))
    (dual_decomposition k ell)
  rw [map_add, map_add, coefficientSharp_contraction_dual, hL, add_zero] at h
  exact h

/-- The factor's fourteen coordinate sections use exactly the projection
matrix of the native primitive Plucker construction. -/
theorem factor_basis (L : Third k →ₗ[k] T) (j : Fin 14) :
    factor k L ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j) =
      ∑ i : Fin 20, projectionMatrix k j i • L (thirdBasis20 k i) := by
  let ell := extension k ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j)
  have hcoord (i : Fin 20) :
      (thirdBasis20 k).coord i ((coefficientDuality k).symm ell) = projectionMatrix k j i := by
    rw [coefficientDuality, Basis.coord_toDualEquiv_symm_apply]
    rw [Basis.coord_apply, Basis.dualBasis_repr]
    change ell (thirdBasis20 k i) = _
    change (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j
      (primitiveProjection k (thirdBasis20 k i)) = _
    simp only [LagrangianPluckerLinear.primitiveBasis14, Basis.dualBasis_apply,
      Basis.map_repr, primitiveProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      projectionMatrix, LinearMap.toMatrix_apply, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  have hs := (thirdBasis20 k).sum_repr ((coefficientDuality k).symm ell)
  have h := congrArg L hs
  simp only [map_sum, map_smul, ← Basis.coord_apply, hcoord] at h
  exact h.symm

end Factor

end M9Native.MukaiPrimitiveDuality

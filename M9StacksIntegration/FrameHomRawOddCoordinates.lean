module

public import M9StacksIntegration.FrameHomRawMatrixCoordinates

/-! The actual tensor exchange in raw evaluation bases, and the rational
coefficient-exchange/matrix-inversion map on the original raw Hom field.
Compatibility with finite descent is a separate assertion. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Module
open scoped Classical TensorProduct

namespace M9Native.FrameHomRawOddCoordinates

open M9.FrameBundleDescent M9.FrameBundleDescent.Standard
open M9.FrameHomFieldDescent M9.DeterminantFrameScalarExtension
open FrameHomRawMatrixCoordinates

local instance ambientCharZero : CharZero Ambient :=
  charZero_of_injective_algebraMap (algebraMap ℂ Ambient).injective

/-- The literal exchange is coefficient transpose and the identity on E0. -/
theorem rawTranspose_coordinates (x : ActualRaw false) (i : Fin 4) :
    rawCoordinates Ambient (actualRawTranspose x) i =
      nativeTranspose (rawCoordinates Ambient x i) := by
  change Ambient ⊗[ℂ] M9.StandardFourPlaneRepresentation.E0 at x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, hx, hy, Pi.add_apply]
  | tmul a v =>
      change rawCoordinates Ambient (nativeTranspose a ⊗ₜ[ℂ] v) i = _
      rw [rawCoordinates_tmul,rawCoordinates_tmul,map_mul,nativeTranspose.commutes]

/-- Tensor-evaluation bases are actually paired by the original exchange. -/
theorem rawTranspose_basis (j : Fin 4) :
    actualRawTranspose (rawBasis false j) = rawBasis true j := by
  apply (rawCoordinates Ambient).injective
  funext i
  rw [rawTranspose_coordinates]
  have hl : rawCoordinates Ambient (rawBasis false j) i = if j = i then 1 else 0 := by
    rw [← rawBasis_repr false,Basis.repr_self_apply]
  have hr : rawCoordinates Ambient (rawBasis true j) i = if j = i then 1 else 0 := by
    rw [← rawBasis_repr true,Basis.repr_self_apply]
  rw [hl,hr]
  split_ifs <;> simp only [map_one,map_zero]

def antiInvariant : Ambient := (M9.FrameInversionRationality.antiInvariant : Ambient)

theorem antiInvariant_ne_zero : antiInvariant ≠ 0 := by
  exact Subtype.coe_ne_coe.mpr M9.FrameInversionRationality.antiInvariant_ne_zero

theorem transpose_antiInvariant : nativeTranspose antiInvariant = -antiInvariant := by
  exact congrArg Subtype.val M9.FrameInversionRationality.exchange_antiInvariant

def matrixInversion : MatrixField ≃+* MatrixField :=
  M9.CayleyFixedField.graphInvolution Ambient nativeTranspose.toRingEquiv
    antiInvariant antiInvariant_ne_zero

theorem matrixInversion_involutive : Function.Involutive matrixInversion :=
  M9.CayleyFixedField.graphInvolution_involutive Ambient nativeTranspose.toRingEquiv
    nativeTranspose_squared antiInvariant antiInvariant_ne_zero

theorem matrixInversion_constant (a : Ambient) :
    matrixInversion (algebraMap Ambient MatrixField a) =
      algebraMap Ambient MatrixField (nativeTranspose a) :=
  M9.CayleyFixedField.graphInvolution_constant Ambient nativeTranspose.toRingEquiv
    antiInvariant antiInvariant_ne_zero a

theorem matrixInversion_matrix :
    (M9.CayleyField.genericMatrix Ambient).map matrixInversion.toRingHom =
      (M9.CayleyField.genericMatrix Ambient)⁻¹ :=
  M9.CayleyFixedField.graphInvolution_matrix Ambient nativeTranspose.toRingEquiv
    antiInvariant antiInvariant_ne_zero transpose_antiInvariant

/-- This rational map is on the actual original raw Hom fraction field. -/
def rawInversion : RawField ≃+* RawField :=
  fieldEquiv.symm.toRingEquiv.trans (matrixInversion.trans fieldEquiv.toRingEquiv)

theorem rawInversion_apply (z : RawField) :
    rawInversion z = fieldEquiv (matrixInversion (fieldEquiv.symm z)) := rfl

theorem fieldEquiv_rawInversion (z : RawField) :
    fieldEquiv.symm (rawInversion z) = matrixInversion (fieldEquiv.symm z) := by
  rw [rawInversion_apply,AlgEquiv.symm_apply_apply]

theorem rawInversion_involutive : Function.Involutive rawInversion := by
  intro z
  rw [rawInversion_apply,fieldEquiv_rawInversion,matrixInversion_involutive,
    AlgEquiv.apply_symm_apply]

theorem rawInversion_constant (a : Ambient) :
    rawInversion (algebraMap Ambient RawField a) =
      algebraMap Ambient RawField (nativeTranspose a) := by
  rw [rawInversion_apply,fieldEquiv.symm.commutes,matrixInversion_constant,
    fieldEquiv.commutes]

theorem rawMatrix_fieldEquiv_symm :
    rawMatrix.map fieldEquiv.symm.toRingHom = M9.CayleyField.genericMatrix Ambient := by
  funext i j
  change fieldEquiv.symm (rawMatrix i j) = _
  rw [← fieldEquiv_matrix,AlgEquiv.symm_apply_apply]
  rfl

theorem rawInversion_matrix :
    rawMatrix.map rawInversion.toRingHom = rawMatrix⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  apply Matrix.map_injective fieldEquiv.symm.injective
  change fieldEquiv.symm.toRingHom.mapMatrix
    ((rawMatrix.map rawInversion.toRingHom) * rawMatrix) =
      fieldEquiv.symm.toRingHom.mapMatrix 1
  rw [map_mul,map_one]
  have hh : (rawMatrix.map rawInversion.toRingHom).map fieldEquiv.symm.toRingHom =
      (M9.CayleyField.genericMatrix Ambient).map matrixInversion.toRingHom := by
    funext i j
    change fieldEquiv.symm (rawInversion (rawMatrix i j)) = _
    rw [fieldEquiv_rawInversion]
    have he := congrFun (congrFun rawMatrix_fieldEquiv_symm i) j
    exact congrArg matrixInversion he
  change ((rawMatrix.map rawInversion.toRingHom).map fieldEquiv.symm.toRingHom) *
    (rawMatrix.map fieldEquiv.symm.toRingHom) = 1
  rw [hh,rawMatrix_fieldEquiv_symm,matrixInversion_matrix]
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (M9.CayleyField.genericMatrix_det_ne_zero Ambient))

/-- The original complex constant field is fixed. -/
theorem rawInversion_complex_constant (c : ℂ) :
    rawInversion (algebraMap ℂ RawField c) = algebraMap ℂ RawField c := by
  rw [IsScalarTower.algebraMap_apply ℂ Ambient RawField,rawInversion_constant,
    nativeTranspose.commutes]

def rawInversionAlgEquiv : RawField ≃ₐ[ℂ] RawField where
  __ := rawInversion
  commutes' := rawInversion_complex_constant

/-- Coefficients and the literal raw matrix determine field homomorphisms. -/
theorem rawFieldHom_ext {E : Type*} [Field E] (f g : RawField →+* E)
    (hc : ∀ a : Ambient, f (algebraMap Ambient RawField a) =
      g (algebraMap Ambient RawField a))
    (hX : ∀ i j : Fin 4, f (rawMatrix i j) = g (rawMatrix i j)) : f = g := by
  have hh : f.comp fieldEquiv.toRingHom = g.comp fieldEquiv.toRingHom := by
    apply M9.CayleyFixedField.rationalHom_ext Ambient
    · intro a
      change f (fieldEquiv (algebraMap Ambient MatrixField a)) =
        g (fieldEquiv (algebraMap Ambient MatrixField a))
      rw [fieldEquiv.commutes]
      exact hc a
    · intro ij
      change f (fieldEquiv (algebraMap PolynomialRing MatrixField (MvPolynomial.X ij))) =
        g (fieldEquiv (algebraMap PolynomialRing MatrixField (MvPolynomial.X ij)))
      rw [fieldEquiv_matrix]
      exact hX ij.1 ij.2
  apply RingHom.ext
  intro z
  have hz := RingHom.congr_fun hh (fieldEquiv.symm z)
  change f (fieldEquiv (fieldEquiv.symm z)) = g (fieldEquiv (fieldEquiv.symm z)) at hz
  simpa only [AlgEquiv.apply_symm_apply] using hz

/-- The original coefficient and actual inverse-matrix laws uniquely pin the
rational odd operator. -/
theorem rawInversion_unique (τ : RawField ≃+* RawField)
    (hc : ∀ a : Ambient, τ (algebraMap Ambient RawField a) =
      algebraMap Ambient RawField (nativeTranspose a))
    (hX : rawMatrix.map τ.toRingHom = rawMatrix⁻¹) : τ = rawInversion := by
  apply RingEquiv.ext
  have hh : τ.toRingHom = rawInversion.toRingHom := rawFieldHom_ext _ _
    (fun a => (hc a).trans (rawInversion_constant a).symm)
    (fun i j => congrFun (congrFun (hX.trans rawInversion_matrix.symm) i) j)
  intro z
  exact congrArg (fun f : RawField →+* RawField => f z) hh

end M9Native.FrameHomRawOddCoordinates

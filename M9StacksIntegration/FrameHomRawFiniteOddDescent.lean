module

public import M9StacksIntegration.FrameHomRawDescendedMatrices
public import M9StacksIntegration.MatrixExchangeConjugation

/-! Actual raw matrix inversion in the genuine paired descended bases. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open scoped Classical

namespace M9Native.FrameHomRawFiniteOddDescent

open M9.FrameBundleDescent M9.FrameBundleDescent.Standard
open M9.FrameHomFieldDescent FrameHomRawMatrixCoordinates
open FrameHomRawOddCoordinates FrameHomRawDescendedMatrices

local instance ambientCharZero : CharZero Ambient :=
  charZero_of_injective_algebraMap (algebraMap ℂ Ambient).injective

theorem rawMatrix_det_ne_zero : rawMatrix.det ≠ 0 := by
  intro hz
  have hh := fieldEquiv.symm.map_det rawMatrix
  rw [hz,map_zero] at hh
  have he : (rawMatrix.map fieldEquiv.symm.toRingHom).det = 0 := hh.symm
  rw [rawMatrix_fieldEquiv_symm] at he
  exact M9.CayleyField.genericMatrix_det_ne_zero Ambient he

theorem inversion_leftField : leftField.val.map rawInversion.toRingHom = rightField.val := by
  ext i j
  change rawInversion (algebraMap Ambient RawField (leftChange.val i j)) =
    algebraMap Ambient RawField (rightChange.val i j)
  rw [rawInversion_constant]
  have hh := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 4) Ambient => U.val i j)
    rightChange_eq_transpose_left
  exact congrArg (algebraMap Ambient RawField) hh.symm

theorem inversion_rightField : rightField.val.map rawInversion.toRingHom = leftField.val := by
  ext i j
  change rawInversion (algebraMap Ambient RawField (rightChange.val i j)) =
    algebraMap Ambient RawField (leftChange.val i j)
  rw [rawInversion_constant]
  have hh := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 4) Ambient => U.val i j)
    rightChange_eq_transpose_left
  change rightChange.val i j = nativeTranspose (leftChange.val i j) at hh
  rw [hh,nativeTranspose_squared]

/-- Literal original invariant coordinate matrix under genuine raw inversion. -/
theorem rawInversion_descendedMatrix :
    descendedMatrix.map rawInversion.toRingHom = descendedMatrix⁻¹ := by
  rw [descendedMatrix_eq]
  exact MatrixExchangeConjugation.inverse_in_paired_bases rawInversion.toRingHom
    leftField rightField rawMatrix inversion_leftField inversion_rightField
      rawInversion_matrix (isUnit_iff_ne_zero.mpr rawMatrix_det_ne_zero)

def fixedMatrix : Matrix (Fin 4) (Fin 4) RawFixedField := fun i j => fixedCoordinate (i,j)

theorem fixedMatrix_coe : fixedMatrix.map RawFixedField.subtype = descendedMatrix := rfl

theorem fixedMatrix_fieldEquiv : fixedMatrix.map fixedFieldEquiv.toRingHom =
    genericIsomMatrix representation := by
  funext i j
  exact fixedFieldEquiv_coordinate (i,j)

/-- Existing actual isomorphism-field exchange, transported only through
its proved genuine finite-frame field equivalence. -/
def fixedInversion : RawFixedField ≃+* RawFixedField :=
  fixedFieldEquiv.toRingEquiv.trans
    ((isomInversion representation).trans fixedFieldEquiv.symm.toRingEquiv)

theorem fixedInversion_apply (z : RawFixedField) :
    fixedInversion z = fixedFieldEquiv.symm
      (isomInversion representation (fixedFieldEquiv z)) := rfl

theorem fixedFieldEquiv_fixedInversion (z : RawFixedField) :
    fixedFieldEquiv (fixedInversion z) =
      isomInversion representation (fixedFieldEquiv z) := by
  rw [fixedInversion_apply,AlgEquiv.apply_symm_apply]

theorem fixedInversion_constant (a : ConnectedField) :
    fixedInversion (algebraMap ConnectedField RawFixedField a) =
      algebraMap ConnectedField RawFixedField (M9.FrameQuadraticExtension.exchange a) := by
  rw [fixedInversion_apply,fixedFieldEquiv.commutes,isomInversion_coefficient,
    fixedFieldEquiv.symm.commutes]

theorem fixedInversion_matrix :
    fixedMatrix.map fixedInversion.toRingHom = fixedMatrix⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  apply Matrix.map_injective fixedFieldEquiv.injective
  change fixedFieldEquiv.toRingHom.mapMatrix
    ((fixedMatrix.map fixedInversion.toRingHom) * fixedMatrix) =
      fixedFieldEquiv.toRingHom.mapMatrix 1
  rw [map_mul,map_one]
  have hh : (fixedMatrix.map fixedInversion.toRingHom).map fixedFieldEquiv.toRingHom =
      (genericIsomMatrix representation).map (isomInversion representation).toRingHom := by
    funext i j
    change fixedFieldEquiv (fixedInversion (fixedCoordinate (i,j))) = _
    rw [fixedFieldEquiv_fixedInversion,fixedFieldEquiv_coordinate]
    rfl
  change ((fixedMatrix.map fixedInversion.toRingHom).map fixedFieldEquiv.toRingHom) *
      (fixedMatrix.map fixedFieldEquiv.toRingHom) = 1
  rw [hh,fixedMatrix_fieldEquiv,isomInversion_matrix]
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (genericIsomMatrix_det_ne_zero representation))

theorem fixedMatrix_det_ne_zero : fixedMatrix.det ≠ 0 := by
  intro hz
  have hh := fixedFieldEquiv.map_det fixedMatrix
  rw [hz,map_zero] at hh
  have he : (fixedMatrix.map fixedFieldEquiv.toRingHom).det = 0 := hh.symm
  rw [fixedMatrix_fieldEquiv] at he
  exact genericIsomMatrix_det_ne_zero representation he

theorem fixedInverseMatrix_coe :
    (fixedMatrix⁻¹).map RawFixedField.subtype = descendedMatrix⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  have hh := congrArg (fun A : Matrix (Fin 4) (Fin 4) RawFixedField =>
      RawFixedField.subtype.mapMatrix A)
    (Matrix.nonsing_inv_mul fixedMatrix (isUnit_iff_ne_zero.mpr fixedMatrix_det_ne_zero))
  change RawFixedField.subtype.mapMatrix (fixedMatrix⁻¹ * fixedMatrix) =
    RawFixedField.subtype.mapMatrix 1 at hh
  rw [map_mul,map_one] at hh
  change (fixedMatrix⁻¹).map RawFixedField.subtype *
    fixedMatrix.map RawFixedField.subtype = 1 at hh
  rw [fixedMatrix_coe] at hh
  exact hh

theorem coe_fixedInversion_matrix :
    fixedMatrix.map (RawFixedField.subtype.comp fixedInversion.toRingHom) = descendedMatrix⁻¹ := by
  change (fixedMatrix.map fixedInversion.toRingHom).map RawFixedField.subtype = _
  rw [fixedInversion_matrix,fixedInverseMatrix_coe]

/-- The original raw odd operator preserves the genuine finite-frame fixed
field and equals its actual isomorphism-field exchange, with the inclusion
retained. No compatibility of these fields is a premise. -/
theorem inclusion_intertwines (z : RawFixedField) :
    rawInversion (z : RawField) = (fixedInversion z : RawField) := by
  let f : RawFixedField →+* RawField := rawInversion.toRingHom.comp RawFixedField.subtype
  let g : RawFixedField →+* RawField := RawFixedField.subtype.comp fixedInversion.toRingHom
  have hc (a : ConnectedField) :
      f (algebraMap ConnectedField RawFixedField a) =
        g (algebraMap ConnectedField RawFixedField a) := by
    change rawInversion ((algebraMap ConnectedField RawFixedField a : RawFixedField) : RawField) =
      ((fixedInversion (algebraMap ConnectedField RawFixedField a) : RawFixedField) : RawField)
    rw [fixedInversion_constant,rawFixedConnectedAlgebra_coe,rawFixedConnectedAlgebra_coe,
      rawInversion_constant]
    rfl
  have hM : fixedMatrix.map f = fixedMatrix.map g := by
    change descendedMatrix.map rawInversion.toRingHom =
      fixedMatrix.map (RawFixedField.subtype.comp fixedInversion.toRingHom)
    rw [rawInversion_descendedMatrix,coe_fixedInversion_matrix]
  have hh : f.comp fixedRationalCoordinates.symm.toRingHom =
      g.comp fixedRationalCoordinates.symm.toRingHom := by
    apply M9.CayleyFixedField.rationalHom_ext ConnectedField
    · intro a
      change f (fixedRationalCoordinates.symm (algebraMap ConnectedField
        (M9.CayleyField.Rational ConnectedField) a)) =
          g (fixedRationalCoordinates.symm (algebraMap ConnectedField
            (M9.CayleyField.Rational ConnectedField) a))
      rw [fixedRationalCoordinates.symm.commutes]
      exact hc a
    · intro ij
      have he : fixedRationalCoordinates.symm
          (M9.CayleyField.genericCoordinate ConnectedField ij) = fixedCoordinate ij := by
        apply fixedRationalCoordinates.injective
        rw [AlgEquiv.apply_symm_apply,fixedRationalCoordinates_coordinate]
      change f (fixedRationalCoordinates.symm (M9.CayleyField.genericCoordinate ConnectedField ij)) =
        g (fixedRationalCoordinates.symm (M9.CayleyField.genericCoordinate ConnectedField ij))
      rw [he]
      exact congrFun (congrFun hM ij.1) ij.2
  have hz := RingHom.congr_fun hh (fixedRationalCoordinates z)
  change f (fixedRationalCoordinates.symm (fixedRationalCoordinates z)) =
    g (fixedRationalCoordinates.symm (fixedRationalCoordinates z)) at hz
  change f z = g z
  simpa only [AlgEquiv.symm_apply_apply] using hz

theorem rawInversion_mem_fixed (z : RawFixedField) : rawInversion z.val ∈ RawFixedField := by
  rw [inclusion_intertwines]
  exact (fixedInversion z).property

/-- Exact finite descent intertwining with the original semilinear inverse. -/
theorem fixedFieldEquiv_intertwines (z : RawFixedField) :
    fixedFieldEquiv (⟨rawInversion z.val,rawInversion_mem_fixed z⟩ : RawFixedField) =
      isomInversion representation (fixedFieldEquiv z) := by
  have he : (⟨rawInversion z.val,rawInversion_mem_fixed z⟩ : RawFixedField) = fixedInversion z :=
    Subtype.ext (inclusion_intertwines z)
  rw [he,fixedFieldEquiv_fixedInversion]

end M9Native.FrameHomRawFiniteOddDescent

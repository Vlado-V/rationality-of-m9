module

public import M9.ConicFourPlaneFrames
public import M9StacksIntegration.ConicFramePolynomial

/-!
# Closed-complex fibers of the literal polynomial conic-frame quotient

The quotient matrix is the original `Q₀ Sym²(adj F)` in coordinate order
`00,11,22,01,02,12`. Its genuine kernel is identified with `F S₀ Fᵀ`, so
the proved tetrahedral frame classification applies to the actual matrix
quotient used in the Grassmannian morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.ConicFrameClosedFiber

open M9.ConicPencilFrames M9.ConicFourPlaneFrames

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev Gamma := M9.TetrahedralGroup.Gamma

/-- The literal kernel of the original polynomial quotient matrix. -/
def matrixKernel (F : Matrix3) : Submodule ℂ (Fin 6 → ℂ) :=
  LinearMap.ker (ConicFrame.quotientMatrix F).mulVecLin

abbrev quotientKernel (F : GL3) : Submodule ℂ (Fin 6 → ℂ) := matrixKernel (F : Matrix3)

/-- The actual polynomial kernel is exactly the actual congruence
four-plane, under the original six symmetric-matrix coordinates. -/
theorem quotientMatrix_kernel_fourPlane (F : GL3) (A : Conic) :
    (ConicFrame.quotientMatrix (F : Matrix3)).mulVec (ConicFrame.symCoordinates A.val) = 0 ↔
      A ∈ fourPlane F := by
  rw [ConicFrame.quotientMatrix_kernel_congruence (F : Matrix3) A.val
    (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero F)) A.property]
  constructor
  · rintro ⟨S, hS, h01, h12, hAS⟩
    refine ⟨⟨S, hS⟩, ⟨h01, h12⟩, ?_⟩
    apply Subtype.ext
    change (conicPush F ⟨S, hS⟩).val = A.val
    rw [conicPush_val]
    exact hAS.symm
  · rintro ⟨S, hS, hSA⟩
    refine ⟨S.val, S.property, hS.1, hS.2, ?_⟩
    have hh := congrArg Subtype.val hSA
    change (F : Matrix3) * S.val * (F : Matrix3).transpose = A.val at hh
    exact hh.symm

theorem quotientKernel_eq_iff_fourPlane_eq (F F' : GL3) :
    quotientKernel F = quotientKernel F' ↔ fourPlane F = fourPlane F' := by
  constructor
  · intro h
    ext A
    rw [← quotientMatrix_kernel_fourPlane F A, ← quotientMatrix_kernel_fourPlane F' A]
    change ConicFrame.symCoordinates A.val ∈ quotientKernel F ↔
      ConicFrame.symCoordinates A.val ∈ quotientKernel F'
    rw [h]
  · intro h
    ext x
    let A : Conic := ⟨ConicFrame.symMatrix x, ConicFrame.symMatrix_transpose x⟩
    have hcoords : ConicFrame.symCoordinates A.val = x := ConicFrame.symCoordinates_symMatrix x
    change (ConicFrame.quotientMatrix (F : Matrix3)).mulVec x = 0 ↔
      (ConicFrame.quotientMatrix (F' : Matrix3)).mulVec x = 0
    rw [← hcoords, quotientMatrix_kernel_fourPlane, quotientMatrix_kernel_fourPlane, h]

/-- Actual equality of polynomial quotient kernels has exactly the
RIGHT tetrahedral frame fibers of the manuscript. -/
theorem quotientKernel_fiber_iff (F F' : GL3) :
    quotientKernel F = quotientKernel F' ↔
      ∃ g : Gamma, ∃ c : ℂ, c ≠ 0 ∧
        (F' : Matrix3) = c • ((F : Matrix3) * M9.TetrahedralGroup.matrix g) := by
  rw [quotientKernel_eq_iff_fourPlane_eq, fourPlane_fiber_iff]

/-- The same classification for literal invertible complex matrices,
without changing their matrix orientation. -/
theorem matrixKernel_fiber_iff (F F' : Matrix3) (hF : F.det ≠ 0) (hF' : F'.det ≠ 0) :
    matrixKernel F = matrixKernel F' ↔
      ∃ g : Gamma, ∃ c : ℂ, c ≠ 0 ∧ F' = c • (F * M9.TetrahedralGroup.matrix g) :=
  quotientKernel_fiber_iff (Matrix.GeneralLinearGroup.mkOfDetNeZero F hF)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero F' hF')

/-- The actual normalized first-row chart fiber of the polynomial
quotient, with no assumed cardinality. -/
def NormalizedKernelFiber (F : GL3) :=
  {F' : GL3 // (F' : Matrix3) 0 0 = 1 ∧ FirstRowNonzero F' ∧ quotientKernel F = quotientKernel F'}

def normalizedKernelFiberEquivFourPlane (F : GL3) :
    NormalizedKernelFiber F ≃ NormalizedFiber F where
  toFun N := ⟨N.val, N.property.1, N.property.2.1,
    (quotientKernel_eq_iff_fourPlane_eq F N.val).mp N.property.2.2⟩
  invFun N := ⟨N.val, N.property.1, N.property.2.1,
    (quotientKernel_eq_iff_fourPlane_eq F N.val).mpr N.property.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The actual twenty-four elements are constructed by normalized
RIGHT translates of the actual tetrahedral matrices. -/
def normalizedKernelFiberEquiv (F : GL3) (hF : FirstRowNonzero F) :
    Gamma ≃ NormalizedKernelFiber F :=
  (normalizedFiberEquiv F hF).trans (normalizedKernelFiberEquivFourPlane F).symm

theorem normalizedKernelFiberEquiv_val (F : GL3) (hF : FirstRowNonzero F) (g : Gamma) :
    ((normalizedKernelFiberEquiv F hF g).val : Matrix3) =
      (((F : Matrix3) * M9.TetrahedralGroup.matrix g) 0 0)⁻¹ •
        ((F : Matrix3) * M9.TetrahedralGroup.matrix g) :=
  normalizedRightFrame_val F hF g

theorem nat_card_normalizedKernelFiber (F : GL3) (hF : FirstRowNonzero F) :
    Nat.card (NormalizedKernelFiber F) = 24 := by
  simpa only [Nat.card_eq_fintype_card, M9.TetrahedralGroup.card_gamma] using
    (Nat.card_congr (normalizedKernelFiberEquiv F hF)).symm

end M9Native.ConicFrameClosedFiber

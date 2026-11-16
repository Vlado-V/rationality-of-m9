module

public import M9StacksIntegration.ConicFramePairSLFixedField
public import M9StacksIntegration.GenericConicHead

/-! Exact identification of the sixteen relative-graph base variables with
the actual native product Grassmannian chart. A graph matrix is the negative
of the normalized quotient's nonpivot block; that sign is retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

open MvPolynomial
open scoped TensorProduct

namespace M9Native.ConicGraphBaseCoordinates

open M9.GraphBundleDescent ConicFramePairRings ConicFrameSourceAlgebra

abbrev NativeIndex := AlgebraicGeometry.Grassmannian.ChartIndex.{0}
  (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding
abbrev GrassField := ConicFramePairFieldComparison.target.functionField
abbrev FrameField := M9.ProjectiveFrameQuotient.projectivePairField

def oneIndexEquiv : (Fin 2 × Fin 4) ≃ NativeIndex :=
  ((Equiv.prodComm _ _).trans finProdFinEquiv).trans
    ConicFrameCoordinateIndex.coordinateEquiv.symm

def blockIndexEquiv : BaseIndex ≃ (NativeIndex ⊕ NativeIndex) where
  toFun b := if b.1 = 0 then .inl (oneIndexEquiv b.2) else .inr (oneIndexEquiv b.2)
  invFun b := Sum.elim (fun a => (0, oneIndexEquiv.symm a))
    (fun a => (1, oneIndexEquiv.symm a)) b
  left_inv b := by
    rcases b with ⟨s,b⟩
    fin_cases s <;> simp
  right_inv b := by
    cases b <;> simp

@[simp] theorem blockIndexEquiv_zero (i : Fin 2) (j : Fin 4) :
    blockIndexEquiv (0,i,j) = .inl (oneIndexEquiv (i,j)) := by
  simp [blockIndexEquiv]

@[simp] theorem blockIndexEquiv_one (i : Fin 2) (j : Fin 4) :
    blockIndexEquiv (1,i,j) = .inr (oneIndexEquiv (i,j)) := by
  simp [blockIndexEquiv]

/-- The exact polynomial chart isomorphism, including the genuine kernel
versus quotient sign. -/
def polynomialEquiv : MvPolynomial BaseIndex ℂ ≃ₐ[ℂ] targetPair ℂ :=
  ((M9.ProjectiveNoName.scaleVariables BaseIndex (-1 : ℂ) (neg_ne_zero.mpr one_ne_zero)).trans
    (MvPolynomial.renameEquiv ℂ blockIndexEquiv)).trans (targetPairEquiv ℂ).symm

theorem polynomialEquiv_zero (i : Fin 2) (j : Fin 4) :
    polynomialEquiv (X (0,i,j)) = -((X (oneIndexEquiv (i,j)) : targetRing ℂ) ⊗ₜ[ℂ] 1) := by
  apply (targetPairEquiv ℂ).injective
  simp [polynomialEquiv, M9.ProjectiveNoName.scaleVariables,
    M9.ProjectiveNoName.scaleHom, targetPairEquiv]

theorem polynomialEquiv_one (i : Fin 2) (j : Fin 4) :
    polynomialEquiv (X (1,i,j)) = -(1 ⊗ₜ[ℂ] (X (oneIndexEquiv (i,j)) : targetRing ℂ)) := by
  apply (targetPairEquiv ℂ).injective
  simp [polynomialEquiv, M9.ProjectiveNoName.scaleVariables,
    M9.ProjectiveNoName.scaleHom, targetPairEquiv]

def tensorFieldEquiv : BaseFunctionField ℂ ≃ₐ[ℂ] targetPairField ℂ :=
  IsFractionRing.algEquivOfAlgEquiv polynomialEquiv

theorem tensorFieldEquiv_polynomial (p : MvPolynomial BaseIndex ℂ) :
    tensorFieldEquiv (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) p) =
      algebraMap (targetPair ℂ) (targetPairField ℂ) (polynomialEquiv p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

/-- The actual native product-Grassmannian generic stalk, through its
proved dense polynomial chart. -/
def nativeBaseEquiv : BaseFunctionField ℂ ≃ₐ[ℂ] GrassField :=
  tensorFieldEquiv.trans ConicFramePairFieldComparison.targetNativeEquiv.symm

/-- The genuine conic-cover pullback of those exact base variables. -/
def baseEmbedding : BaseFunctionField ℂ →ₐ[ℂ] FrameField :=
  ConicFramePairSLFixedField.projectiveEmbedding.comp nativeBaseEquiv.toAlgHom

theorem baseEmbedding_deck_fixed (a b : M9.TetrahedralGroup.Gamma)
    (z : BaseFunctionField ℂ) :
    PairProjectiveEquivariance.projectivePairDeck a b (baseEmbedding z) = baseEmbedding z := by
  apply Subtype.ext
  exact ConicFramePairSLFixedField.projectiveEmbedding_deck_fixed a b (nativeBaseEquiv z)

theorem exists_baseEmbedding (z : FrameField)
    (hz : ∀ a b : M9.TetrahedralGroup.Gamma,
      PairProjectiveEquivariance.projectivePairDeck a b z = z) :
    ∃ x : BaseFunctionField ℂ, baseEmbedding x = z := by
  obtain ⟨x,hx⟩ := ConicFramePairSLFixedField.exists_projectiveEmbedding z
    (fun a b => congrArg Subtype.val (hz a b))
  refine ⟨nativeBaseEquiv.symm x, ?_⟩
  change ConicFramePairSLFixedField.projectiveEmbedding (nativeBaseEquiv (nativeBaseEquiv.symm x)) = z
  rw [AlgEquiv.apply_symm_apply]
  exact hx

end M9Native.ConicGraphBaseCoordinates

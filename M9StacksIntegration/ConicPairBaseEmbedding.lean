module

public import M9StacksIntegration.ConicPairMovingFrames

/-! The actual conic-cover inclusion takes the original sixteen graph-base
variables to the actual two moving-plane cell matrices in the original
independent frame-pair field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open MvPolynomial
open scoped Classical TensorProduct

namespace M9Native.ConicPairBaseEmbedding

open M9.GraphBundleDescent ConicGraphBaseCoordinates
open ConicFramePairRings ConicFramePairFixedField ConicFrameSourceAlgebra
open ConicPairMovingFrames GenericConicBaseCoordinates

theorem embedding_polynomial (p : MvPolynomial BaseIndex ℂ) :
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) p) =
      PairProjectiveRatios.pairProjectiveEquiv (sourceToNested
        (pairFieldEmbedding ℂ (algebraMap (targetPair ℂ) (targetPairField ℂ) (polynomialEquiv p)))) := by
  change PairProjectiveRatios.pairProjectiveEquiv (sourceToNested
    (pairFieldEmbedding ℂ (ConicFramePairFieldComparison.targetNativeEquiv
      (ConicFramePairFieldComparison.targetNativeEquiv.symm
        (tensorFieldEquiv (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) p)))))) = _
  rw [AlgEquiv.apply_symm_apply, tensorFieldEquiv_polynomial]

theorem source_left (b : sourceRing ℂ) :
    PairProjectiveRatios.pairProjectiveEquiv (sourceToNested (leftSourceEmbedding b)) =
      firstEmbedding (toRationalAlgHom ℂ b) := by
  have h := (congrArg sourceToNested (leftFieldEmbedding_toRational b).symm).trans
    (sourceToNested_leftField (toRationalAlgHom ℂ b))
  exact congrArg PairProjectiveRatios.pairProjectiveEquiv h

theorem source_right (b : sourceRing ℂ) :
    PairProjectiveRatios.pairProjectiveEquiv (sourceToNested (rightSourceEmbedding b)) =
      secondEmbedding (toRationalAlgHom ℂ b) := by
  have h := (congrArg sourceToNested (rightFieldEmbedding_toRational b).symm).trans
    (sourceToNested_rightField (toRationalAlgHom ℂ b))
  exact congrArg PairProjectiveRatios.pairProjectiveEquiv h

theorem baseEmbedding_zero_quotient (i : Fin 2) (j : Fin 4) :
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X (0,i,j))) =
      -firstEmbedding (ConicFrameCoordinates.coordinate ℂ (finProdFinEquiv (j,i))) := by
  let b := sourceCoordinate ℂ (finProdFinEquiv (j,i))
  have hc : coordinatePairMap ℂ
      (-((X (oneIndexEquiv (i,j)) : targetRing ℂ) ⊗ₜ[ℂ] 1)) = -(b ⊗ₜ[ℂ] 1) := by
    simp only [map_neg, coordinatePairMap, Algebra.TensorProduct.map_tmul,
      coordinateMap, aeval_X, map_one, oneIndex_coordinate]
    rfl
  let ψ : sourcePair ℂ →ₐ[ℂ] ConicPairMovingFrames.B :=
    (PairProjectiveRatios.pairProjectiveEquiv.toAlgHom.comp sourceToNested.toAlgHom).comp
      (IsScalarTower.toAlgHom ℂ (sourcePair ℂ) SourceField)
  calc
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X (0,i,j))) =
        ψ (coordinatePairMap ℂ (-((X (oneIndexEquiv (i,j)) : targetRing ℂ) ⊗ₜ[ℂ] 1))) := by
      rw [embedding_polynomial, polynomialEquiv_zero, pairFieldEmbedding_algebraMap]
      rfl
    _ = ψ (-(b ⊗ₜ[ℂ] 1)) := congrArg ψ hc
    _ = -ψ (b ⊗ₜ[ℂ] 1) := ψ.map_neg _
    _ = -firstEmbedding (toRationalAlgHom ℂ b) := congrArg Neg.neg (source_left b)
    _ = _ := congrArg (fun z => -firstEmbedding z)
      (toRational_sourceCoordinate ℂ (finProdFinEquiv (j,i)))

theorem baseEmbedding_one_quotient (i : Fin 2) (j : Fin 4) :
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X (1,i,j))) =
      -secondEmbedding (ConicFrameCoordinates.coordinate ℂ (finProdFinEquiv (j,i))) := by
  let b := sourceCoordinate ℂ (finProdFinEquiv (j,i))
  have hc : coordinatePairMap ℂ
      (-(1 ⊗ₜ[ℂ] (X (oneIndexEquiv (i,j)) : targetRing ℂ))) = -(1 ⊗ₜ[ℂ] b) := by
    simp only [map_neg, coordinatePairMap, Algebra.TensorProduct.map_tmul,
      coordinateMap, aeval_X, map_one, oneIndex_coordinate]
    rfl
  let ψ : sourcePair ℂ →ₐ[ℂ] ConicPairMovingFrames.B :=
    (PairProjectiveRatios.pairProjectiveEquiv.toAlgHom.comp sourceToNested.toAlgHom).comp
      (IsScalarTower.toAlgHom ℂ (sourcePair ℂ) SourceField)
  calc
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X (1,i,j))) =
        ψ (coordinatePairMap ℂ (-(1 ⊗ₜ[ℂ] (X (oneIndexEquiv (i,j)) : targetRing ℂ)))) := by
      rw [embedding_polynomial, polynomialEquiv_one, pairFieldEmbedding_algebraMap]
      rfl
    _ = ψ (-(1 ⊗ₜ[ℂ] b)) := congrArg ψ hc
    _ = -ψ (1 ⊗ₜ[ℂ] b) := ψ.map_neg _
    _ = -secondEmbedding (toRationalAlgHom ℂ b) := congrArg Neg.neg (source_right b)
    _ = _ := congrArg (fun z => -secondEmbedding z)
      (toRational_sourceCoordinate ℂ (finProdFinEquiv (j,i)))

theorem baseEmbedding_zero (i : Fin 2) (j : Fin 4) :
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X (0,i,j))) =
      planeMatrix 0 i j := by
  rw [baseEmbedding_zero_quotient, coordinate_eq_neg_genericPlane]
  exact (congrArg Neg.neg (firstEmbedding.map_neg _)).trans (neg_neg _)

theorem baseEmbedding_one (i : Fin 2) (j : Fin 4) :
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X (1,i,j))) =
      planeMatrix 1 i j := by
  rw [baseEmbedding_one_quotient, coordinate_eq_neg_genericPlane]
  exact (congrArg Neg.neg (secondEmbedding.map_neg _)).trans (neg_neg _)

theorem baseEmbedding_entry (s : Fin 2) (i : Fin 2) (j : Fin 4) :
    baseEmbedding (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X (s,i,j))) =
      planeMatrix s i j := by
  fin_cases s
  · exact baseEmbedding_zero i j
  · exact baseEmbedding_one i j

end M9Native.ConicPairBaseEmbedding

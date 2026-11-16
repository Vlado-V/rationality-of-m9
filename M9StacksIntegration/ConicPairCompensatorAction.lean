module

public import M9StacksIntegration.GenericConicCompensatorGamma
public import M9StacksIntegration.ConicRawGammaMatrices
public import M9StacksIntegration.ConicGraphCoefficientDescent

/-! Exact original deck action on both actual pair compensators. The
four-dimensional matrices are the proved literal E₀ representation. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

open Matrix
open scoped Classical TensorProduct

namespace M9Native.ConicPairCompensatorAction

open M9.GraphBundleDescent M9.StandardFourPlaneRepresentation
open M9.DeterminantFrameScalarExtension M9.DeterminantFrameScalarEquivariance
open GenericConicHead ConicPairMovingFrames ConicRawGammaMatrices

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

theorem genericCompensator_image (g : M9.TetrahedralGroup.Gamma) :
    Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
      genericCompensatedFrame = genericCompensatedFrame * gammaK L g := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  obtain ⟨x,hx⟩ := (rawCoordinates L).surjective (Pi.single j 1)
  have hv :
      (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
        genericCompensatedFrame).val.mulVec (rawCoordinates L x) =
          (genericCompensatedFrame * gammaK L g).val.mulVec (rawCoordinates L x) :=
    (GenericConicCompensatorGamma.compensator_image_action g x).trans
      ((congrArg genericCompensatedFrame.val.mulVec
        (gammaK_mulVec_rawCoordinates L g x).symm).trans (Matrix.mulVec_mulVec _ _ _))
  exact (congrArg
    (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
      genericCompensatedFrame).val.mulVec hx).symm.trans
    (hv.trans (congrArg (genericCompensatedFrame * gammaK L g).val.mulVec hx))

theorem firstEmbedding_deck (a b : M9.TetrahedralGroup.Gamma) (x : L) :
    PairProjectiveEquivariance.projectivePairDeck a b (firstEmbedding x) =
      firstEmbedding (ConicFrameRationalGamma.rationalRepresentation a x) := by
  have h := PairProjectiveEquivariance.pairProjectiveEquiv_pairDeck a b
    (ConicFrameIndependentPairAction.coefficientEmbedding x)
  exact h.symm.trans (congrArg PairProjectiveRatios.pairProjectiveEquiv
    (ConicFrameIndependentPairAction.pairRepresentation_coefficient (a,b) x))

theorem secondEmbedding_deck (a b : M9.TetrahedralGroup.Gamma) (x : L) :
    PairProjectiveEquivariance.projectivePairDeck a b (secondEmbedding x) =
      secondEmbedding (ConicFrameRationalGamma.rationalRepresentation b x) := by
  have h := PairProjectiveEquivariance.pairProjectiveEquiv_pairDeck a b
    (ConicFrameIndependentPairAction.outerEmbedding x)
  exact h.symm.trans (congrArg PairProjectiveRatios.pairProjectiveEquiv
    (ConicFrameIndependentPairAction.pairRepresentation_outer (a,b) x))

theorem compensatedFrame_deck_zero (a b : M9.TetrahedralGroup.Gamma) :
    Matrix.GeneralLinearGroup.map (PairProjectiveEquivariance.projectivePairDeck a b).toRingHom
      (compensatedFrame 0) = compensatedFrame 0 * gammaK B a := by
  have hm : Matrix.GeneralLinearGroup.map
      (PairProjectiveEquivariance.projectivePairDeck a b).toRingHom (compensatedFrame 0) =
      Matrix.GeneralLinearGroup.map firstEmbedding.toRingHom
        (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation a).toRingHom
          genericCompensatedFrame) := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact firstEmbedding_deck a b (genericCompensatedFrame.val i j)
  calc
    _ = Matrix.GeneralLinearGroup.map firstEmbedding.toRingHom
        (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation a).toRingHom
          genericCompensatedFrame) := hm
    _ = Matrix.GeneralLinearGroup.map firstEmbedding.toRingHom
        (genericCompensatedFrame * gammaK L a) :=
      congrArg (Matrix.GeneralLinearGroup.map firstEmbedding.toRingHom) (genericCompensator_image a)
    _ = Matrix.GeneralLinearGroup.map firstEmbedding.toRingHom genericCompensatedFrame *
        Matrix.GeneralLinearGroup.map firstEmbedding.toRingHom (gammaK L a) := map_mul _ _ _
    _ = _ := congrArg (fun u => compensatedFrame 0 * u) (map_gammaK L firstEmbedding a)

theorem compensatedFrame_deck_one (a b : M9.TetrahedralGroup.Gamma) :
    Matrix.GeneralLinearGroup.map (PairProjectiveEquivariance.projectivePairDeck a b).toRingHom
      (compensatedFrame 1) = compensatedFrame 1 * gammaK B b := by
  have hm : Matrix.GeneralLinearGroup.map
      (PairProjectiveEquivariance.projectivePairDeck a b).toRingHom (compensatedFrame 1) =
      Matrix.GeneralLinearGroup.map secondEmbedding.toRingHom
        (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation b).toRingHom
          genericCompensatedFrame) := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact secondEmbedding_deck a b (genericCompensatedFrame.val i j)
  calc
    _ = Matrix.GeneralLinearGroup.map secondEmbedding.toRingHom
        (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation b).toRingHom
          genericCompensatedFrame) := hm
    _ = Matrix.GeneralLinearGroup.map secondEmbedding.toRingHom
        (genericCompensatedFrame * gammaK L b) :=
      congrArg (Matrix.GeneralLinearGroup.map secondEmbedding.toRingHom) (genericCompensator_image b)
    _ = Matrix.GeneralLinearGroup.map secondEmbedding.toRingHom genericCompensatedFrame *
        Matrix.GeneralLinearGroup.map secondEmbedding.toRingHom (gammaK L b) := map_mul _ _ _
    _ = _ := congrArg (fun u => compensatedFrame 1 * u) (map_gammaK L secondEmbedding b)

theorem frameRepresentation_eq (g : ConicGraphCoefficientDescent.G) :
    ConicGraphCoefficientDescent.frameRepresentation g =
      PairProjectiveEquivariance.projectivePairDeck g.1 g.2 := by
  apply AlgEquiv.ext
  exact ConicGraphCoefficientDescent.frameRepresentation_apply g

theorem compensatedFrame_action (g : ConicGraphCoefficientDescent.G) (s : Fin 2) :
    Matrix.GeneralLinearGroup.map (ConicGraphCoefficientDescent.frameRepresentation g).toRingHom
      (compensatedFrame s) = compensatedFrame s * gammaK B (![g.1,g.2] s) := by
  rw [frameRepresentation_eq]
  fin_cases s
  · exact compensatedFrame_deck_zero g.1 g.2
  · exact compensatedFrame_deck_one g.1 g.2

end M9Native.ConicPairCompensatorAction

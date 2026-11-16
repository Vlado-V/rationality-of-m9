module

public import M9StacksIntegration.MukaiConormalChartCovariance
public import M9StacksIntegration.MukaiConormalChartFrame
public import M9StacksIntegration.MukaiConormalOriginFrame

/-! Actual positive primitive point coordinates in the original
translated determinant frame. Coefficient duality is retained: their
evaluation functional is the literal original section-value map. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module Matrix
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.MukaiConormalPositivePoint

open MukaiConormalChartJets MukaiConormalChartCovariance
open LagrangianTranslatedDeterminantCoordinates LagrangianTranslatedDeterminantSections
open LagrangianTranslatedCharts LagrangianPluckerQuotient LagrangianSigmaInvariance

variable (K : Type u) [Field K] [CharZero K]

def positivePoint (z : Spec (.of K) ⟶ chart K) (g : Matrix.symplecticGroup (Fin 3) K) :
    LagrangianField.Primitive K :=
  (LagrangianPluckerLinear.primitiveBasis14 K).equivFun.symm
    (valueVector K z (sectionTuple K g))

theorem positivePoint_coordinates (z : Spec (.of K) ⟶ chart K)
    (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    (LagrangianPluckerLinear.primitiveBasis14 K).equivFun (positivePoint K z g) j =
      value K z (sectionTuple K g j) :=
  congrFun ((LagrangianPluckerLinear.primitiveBasis14 K).equivFun.apply_symm_apply _) j

/-- The positive vector represents the actual original framed
primitive determinant quotient through coefficient evaluation. -/
theorem positivePoint_eval (z : Spec (.of K) ⟶ chart K)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    Module.Dual.eval K (LagrangianField.Primitive K) (positivePoint K z g) =
      valueMap K z (sectionTuple K g) := by
  apply LinearMap.ext
  intro ell
  change ell (positivePoint K z g) =
    ∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) * value K z (sectionTuple K g j)
  let b := LagrangianPluckerLinear.primitiveBasis14 K
  calc
    _ = ell (∑ j : Fin 14, b.equivFun (positivePoint K z g) j • b j) :=
      congrArg ell (b.sum_repr _).symm
    _ = _ := by
      simp only [map_sum,map_smul,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [positivePoint_coordinates]
      exact mul_comm _ _

/-- The literal actual positive primitive action, with the same field
point and actual determinant frames on both translated charts. -/
theorem positivePoint_mul (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 _) (g h : Matrix.symplecticGroup (Fin 3) K) :
    positivePoint K z (g*h) =
      PrimitiveCoefficientAction.primitiveAction K (transposeSymplectic K h) (positivePoint K z g) := by
  apply (LagrangianPluckerLinear.primitiveBasis14 K).equivFun.injective
  funext j
  calc
    _ = value K z (sectionTuple K (g*h) j) := positivePoint_coordinates K z (g*h) j
    _ = ∑ k, positiveMatrix K h j k * value K z (sectionTuple K g k) :=
      value_mul K z hz g h j
    _ = (PrimitiveRingMatrices.matrix14 K K (RingHom.id K) (transposeSymplectic K h) *ᵥ
        (LagrangianPluckerLinear.primitiveBasis14 K).equivFun (positivePoint K z g)) j := by
      simp only [Matrix.mulVec,dotProduct,positiveMatrix]
      apply Finset.sum_congr rfl
      intro k _
      rw [positivePoint_coordinates]
    _ = _ := congrFun (PrimitiveCoefficientMatrices.matrix14_native K
      (transposeSymplectic K h) (positivePoint K z g)) j

theorem positivePoint_span_mul (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 _) (g h : Matrix.symplecticGroup (Fin 3) K) :
    Submodule.span K {positivePoint K z (g*h)} =
      (Submodule.span K {positivePoint K z g}).map
        (PrimitiveCoefficientAction.primitiveAction K (transposeSymplectic K h)).toLinearMap := by
  rw [positivePoint_mul K z hz g h,Submodule.map_span,Set.image_singleton]
  simp only [LinearEquiv.coe_coe,LinearEquiv.coe_toLinearMap]

/-- The vector coordinates are those of the actual point determinant
frame obtained from the original quotient frame by genuine pullback. -/
theorem positivePoint_pointFrame (z : Spec (.of K) ⟶ chart K)
    (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    (LagrangianPluckerLinear.primitiveBasis14 K).equivFun (positivePoint K z g) j =
      (Scheme.ΓSpecIso (.of K)).hom
        (show Γ(Spec (.of K),⊤) from
          (MukaiConormalChartFrame.pointDeterminantFrame K (translatedBigCell K g)
            (translatedDeterminantIso K g) z).hom.app ⊤
              (pullbackGlobalSections (z ≫ translatedBigCell K g) (determinantLine K)
                (primitiveSections K j))) := by
  rw [positivePoint_coordinates,MukaiConormalChartFrame.pointDeterminantFrame_coordinate]
  rfl

/-- The original acted quotient matrix at the literal polynomial
origin is exactly [I|0] times the original native symplectic matrix. -/
theorem translatedMatrix_origin (g : Matrix.symplecticGroup (Fin 3) K) :
    (translatedMatrix K g).map (MukaiConormalBigCellFirstJet.originEval K).toRingHom =
      LagrangianPluckerFirstJet.standard K 0 * LagrangianTransitivity.matrixSix K g := by
  rw [translatedMatrix,Matrix.map_mul,MukaiConormalBigCellFirstJet.graphQuotient_origin,
    LagrangianTransitivity.matrixSix_map,Matrix.map_map]
  congr 1
  ext i j
  exact (MukaiConormalBigCellFirstJet.originEval K).commutes _

/-- The original zero chart point in the actual unacted frame is the
original primitive scalar vector, rather than a separately chosen line. -/
theorem positivePoint_origin_one :
    positivePoint K (MukaiConormalOriginFrame.zeroPoint K) 1 =
      MukaiConormalOrigin.originPoint K := by
  have hm : positiveMatrix K (1 : Matrix.symplecticGroup (Fin 3) K) = 1 := by
    rw [positiveMatrix,LagrangianTranslatedDeterminantCoordinates.transpose_one,
      PrimitiveRingMatrices.matrix14_one]
  have hp : translatedPolynomial K (1 : Matrix.symplecticGroup (Fin 3) K) =
      MukaiConormalBigCellSections.sectionPolynomial K := by
    rw [translatedPolynomial_native,hm]
    rw [Matrix.map_one (MvPolynomial.C : K →+* MvPolynomial (Fin 6) K)
      (map_zero _) (map_one _),Matrix.one_mulVec]
  apply (LagrangianPluckerLinear.primitiveBasis14 K).equivFun.injective
  funext j
  rw [positivePoint_coordinates]
  have hs : sectionTuple K (1 : Matrix.symplecticGroup (Fin 3) K) j =
      MukaiConormalBigCellSections.scalarEquiv K
        (MukaiConormalBigCellSections.sectionPolynomial K j) := by
    calc
      _ = MukaiConormalBigCellSections.scalarEquiv K (translatedPolynomial K 1 j) :=
        translatedDeterminantIso_coordinate K 1 j
      _ = _ := congrArg (MukaiConormalBigCellSections.scalarEquiv K) (congrFun hp j)
  calc
    _ = (MukaiConormalBigCellFirstJet.originEval K)
        (MukaiConormalBigCellSections.sectionPolynomial K j) := by
      change (Scheme.ΓSpecIso (.of K)).hom
        ((MukaiConormalOriginFrame.zeroPoint K).appTop (sectionTuple K 1 j)) = _
      rw [hs,MukaiConormalOriginFrame.zeroPoint_scalar]
      exact (Scheme.ΓSpecIso (.of K)).inv_hom_id_apply _
    _ = _ := MukaiConormalBigCellFirstJet.sectionPolynomial_origin_primitive K j

/-- Actual translated-origin determinant coordinates are the literal
positive native primitive action of the original symplectic matrix. -/
theorem positivePoint_origin (g : Matrix.symplecticGroup (Fin 3) K) :
    positivePoint K (MukaiConormalOriginFrame.zeroPoint K) g =
      PrimitiveCoefficientAction.primitiveAction K (transposeSymplectic K g)
        (MukaiConormalOrigin.originPoint K) := by
  have hz : MukaiConormalOriginFrame.zeroPoint K ≫ chartProjection K = 𝟙 _ := by
    have h := MukaiConormalOriginFrame.origin_over_base K
    change (MukaiConormalOriginFrame.zeroPoint K ≫ LagrangianMatrixChart.bigCell K) ≫
      LagrangianGrassmannian.projection K = 𝟙 _ at h
    rw [Category.assoc,LagrangianMatrixChart.bigCell_projection] at h
    exact h
  simpa only [one_mul,positivePoint_origin_one] using
    positivePoint_mul K (MukaiConormalOriginFrame.zeroPoint K) hz 1 g

end M9Native.MukaiConormalPositivePoint

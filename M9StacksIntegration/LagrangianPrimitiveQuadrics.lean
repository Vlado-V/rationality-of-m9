module

public import M9StacksIntegration.LagrangianRingCoordinateEntries
public import M9StacksIntegration.LagrangianBlockMinorSymmetry
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away

/-! The actual twenty-one homogeneous quadratic polynomials in the
original primitive basis. Their arbitrary-ring evaluations on isotropic
row quotients vanish, with the original finite basis reindex retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open MvPolynomial Matrix

universe u

namespace M9Native.LagrangianPrimitiveQuadrics

open LagrangianQuadricChartAlgebra (SymIndex)
open LagrangianBlockMinorQuadrics LagrangianBlockMinorSymmetry

/-- The exact block-index equivalence, followed by the original frozen
coordinateBasis14 reindex; no numerical numbering is substituted. -/
def blockIndexEquiv : LagrangianHomogeneousQuadrics.CoordinateIndex.{u} ≃
    LagrangianField.CoordinateIndex :=
  Equiv.sumCongr (Equiv.refl Unit)
    (Equiv.sumCongr Equiv.ulift
      (Equiv.sumCongr Equiv.ulift (Equiv.refl Unit)))

def coordinateIndexEquiv : LagrangianHomogeneousQuadrics.CoordinateIndex.{u} ≃ Fin 14 :=
  blockIndexEquiv.trans LagrangianCoordinateBasisEntries.indexEquiv

variable (K : Type u) [Field K]

def quadric (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    MvPolynomial (Fin 14) K :=
  MvPolynomial.rename coordinateIndexEquiv (LagrangianHomogeneousQuadrics.quadric K i)

theorem quadric_homogeneous (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    (quadric K i).IsHomogeneous 2 :=
  (LagrangianHomogeneousQuadrics.quadric_homogeneous K i).rename_isHomogeneous

def form (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K 13 2 :=
  ⟨quadric K i, quadric_homogeneous K i⟩

variable {K} {R : Type u} [CommRing R] (κ : K →+* R)
    (M : Matrix (Fin 3) (Fin 6) R)

def blockEvaluation : LagrangianHomogeneousQuadrics.Ring K →+* R :=
  MvPolynomial.eval₂Hom κ
    (fun i => LagrangianRing.rowFourteen R κ M (coordinateIndexEquiv i))

theorem blockEvaluation_a :
    blockEvaluation κ M (LagrangianHomogeneousQuadrics.aVariable K) = aMinor R M := by
  rw [blockEvaluation, LagrangianHomogeneousQuadrics.aVariable, MvPolynomial.eval₂Hom_X']
  exact LagrangianRingCoordinateEntries.rowFourteen_entry κ M (Sum.inl ())

theorem blockEvaluation_b :
    blockEvaluation κ M (LagrangianHomogeneousQuadrics.bVariable K) = bMinor R M := by
  rw [blockEvaluation, LagrangianHomogeneousQuadrics.bVariable, MvPolynomial.eval₂Hom_X']
  exact LagrangianRingCoordinateEntries.rowFourteen_entry κ M
    (Sum.inr (Sum.inr (Sum.inr ())))

theorem blockEvaluation_pMatrix
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) :
    (LagrangianHomogeneousQuadrics.pMatrix K).map (blockEvaluation κ M) = pMinors R M := by
  funext i j
  rw [Matrix.map_apply, LagrangianHomogeneousQuadrics.pMatrix,
    blockEvaluation, MvPolynomial.eval₂Hom_X']
  have he := LagrangianRingCoordinateEntries.rowFourteen_entry κ M
    (Sum.inr (Sum.inr (Sum.inl (LagrangianMatrixChart.symmetricIndex (i,j)))))
  change _ = pMinors R M _ _ at he
  refine he.trans ?_
  by_cases hij : i ≤ j
  · simp only [LagrangianMatrixChart.symmetricIndex, dite_eq_left hij]
  · simp only [LagrangianMatrixChart.symmetricIndex, dite_eq_right hij]
    exact congrFun (congrFun (pMinors_symmetric R M hM) i) j

theorem blockEvaluation_qMatrix
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) :
    (LagrangianHomogeneousQuadrics.qMatrix K).map (blockEvaluation κ M) = qMinors R M := by
  funext i j
  rw [Matrix.map_apply, LagrangianHomogeneousQuadrics.qMatrix,
    blockEvaluation, MvPolynomial.eval₂Hom_X']
  have he := LagrangianRingCoordinateEntries.rowFourteen_entry κ M
    (Sum.inr (Sum.inl (LagrangianMatrixChart.symmetricIndex (i,j))))
  change _ = qMinors R M _ _ at he
  refine he.trans ?_
  by_cases hij : i ≤ j
  · simp only [LagrangianMatrixChart.symmetricIndex, dite_eq_left hij]
  · simp only [LagrangianMatrixChart.symmetricIndex, dite_eq_right hij]
    exact congrFun (congrFun (qMinors_symmetric R M hM) i) j

theorem blockEvaluation_adjP
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) (i j : Fin 3) :
    blockEvaluation κ M (LagrangianHomogeneousQuadrics.adjP K i j) = 0 := by
  have ha := (blockEvaluation κ M).map_adjugate (LagrangianHomogeneousQuadrics.pMatrix K)
  simp only [RingHom.mapMatrix_apply] at ha
  rw [blockEvaluation_pMatrix κ M hM] at ha
  have hae := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i j) ha
  have hp := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i j)
    (adjugate_pMinors R M)
  rw [LagrangianHomogeneousQuadrics.adjP, map_sub, map_mul, blockEvaluation_a]
  rw [show blockEvaluation κ M ((LagrangianHomogeneousQuadrics.pMatrix K).adjugate i j) =
    (pMinors R M).adjugate i j from hae]
  rw [show blockEvaluation κ M (LagrangianHomogeneousQuadrics.qMatrix K i j) =
    qMinors R M i j from congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i j)
      (blockEvaluation_qMatrix κ M hM)]
  simpa only [Matrix.smul_apply, smul_eq_mul] using sub_eq_zero.mpr hp

theorem blockEvaluation_adjQ
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) (i j : Fin 3) :
    blockEvaluation κ M (LagrangianHomogeneousQuadrics.adjQ K i j) = 0 := by
  have ha := (blockEvaluation κ M).map_adjugate (LagrangianHomogeneousQuadrics.qMatrix K)
  simp only [RingHom.mapMatrix_apply] at ha
  rw [blockEvaluation_qMatrix κ M hM] at ha
  have hae := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i j) ha
  have hp := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i j)
    (adjugate_qMinors R M)
  rw [LagrangianHomogeneousQuadrics.adjQ, map_sub, map_mul, blockEvaluation_b]
  rw [show blockEvaluation κ M ((LagrangianHomogeneousQuadrics.qMatrix K).adjugate i j) =
    (qMinors R M).adjugate i j from hae]
  rw [show blockEvaluation κ M (LagrangianHomogeneousQuadrics.pMatrix K i j) =
    pMinors R M i j from congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i j)
      (blockEvaluation_pMatrix κ M hM)]
  simpa only [Matrix.smul_apply, smul_eq_mul] using sub_eq_zero.mpr hp

theorem blockEvaluation_product
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0) (i j : Fin 3) :
    blockEvaluation κ M (LagrangianHomogeneousQuadrics.product K i j) = 0 := by
  have hm : (LagrangianHomogeneousQuadrics.pMatrix K *
      LagrangianHomogeneousQuadrics.qMatrix K).map (blockEvaluation κ M) =
      (aMinor R M * bMinor R M) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    rw [Matrix.map_mul, blockEvaluation_pMatrix κ M hM, blockEvaluation_qMatrix κ M hM,
      product_pMinors_qMinors]
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A i j) hm
  have ho : blockEvaluation κ M ((1 : Matrix (Fin 3) (Fin 3)
      (LagrangianHomogeneousQuadrics.Ring K)) i j) =
      (1 : Matrix (Fin 3) (Fin 3) R) i j := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero]
  rw [LagrangianHomogeneousQuadrics.product, map_sub, map_mul, map_mul,
    blockEvaluation_a, blockEvaluation_b, ho]
  exact sub_eq_zero.mpr he

theorem blockEvaluation_quadric
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    blockEvaluation κ M (LagrangianHomogeneousQuadrics.quadric K i) = 0 := by
  cases i with
  | inl ij => exact blockEvaluation_adjP κ M hM _ _
  | inr i =>
    cases i with
    | inl ij => exact blockEvaluation_adjQ κ M hM _ _
    | inr ij => exact blockEvaluation_product κ M hM _ _

/-- Genuine original-basis polynomial equations on every isotropic
row quotient over every coefficient ring, including nonreduced rings. -/
theorem eval₂_quadric_eq_zero
    (hM : ∀ i j, LagrangianRing.omega R (M i) (M j) = 0)
    (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    MvPolynomial.eval₂Hom κ (LagrangianRing.rowFourteen R κ M) (quadric K i) = 0 := by
  rw [quadric, MvPolynomial.eval₂Hom_rename]
  exact blockEvaluation_quadric κ M hM i

end M9Native.LagrangianPrimitiveQuadrics

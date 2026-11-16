module

public import M9.ProjectiveFrameAction
public import M9.FrameProjectiveRatios

/-!
# The original pair-frame decks on the native projective quotient

All deck maps below are genuine automorphisms of the original iterated
rational pair field. Their action is compared with the actual native
generic-stalk action through the proved projective connected quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

open scoped Classical Matrix BigOperators

namespace M9.FrameQuotientActionComparison

open MvPolynomial Matrix FrameFieldElimination ProjectiveFrameQuotient
open FrameProjectiveGeometry ProjectiveFunctionField

abbrev Gamma := TetrahedralGroup.Gamma
abbrev W := FrameAction.TetrahedralFrameGroup

section ActualDecks

variable (A : Type*) [Field A] [Algebra ℂ A]

/-- Literal right multiplication of one independent generic frame. -/
def rightFractionEquiv (a : ConstantFrameElimination.GLn ℂ 3) :
    ConstantFrameElimination.FunctionField A 3 ≃ₐ[A]
      ConstantFrameElimination.FunctionField A 3 :=
  transposeFractionEquiv A *
    ConstantFrameElimination.leftFractionEquiv ℂ A 3 (FrameAction.contragredient a⁻¹) *
      transposeFractionEquiv A

/-- Each original generic entry is sent to the corresponding entry of `F a`. -/
theorem rightFractionEquiv_variable (a : ConstantFrameElimination.GLn ℂ 3) (i j : Fin 3) :
    rightFractionEquiv A a
        (algebraMap (ConstantFrameElimination.PolynomialRing A 3)
          (ConstantFrameElimination.FunctionField A 3) (X (i,j))) =
      ∑ k : Fin 3,
        algebraMap A (ConstantFrameElimination.FunctionField A 3)
            (algebraMap ℂ A (a.val k j)) *
          algebraMap (ConstantFrameElimination.PolynomialRing A 3)
            (ConstantFrameElimination.FunctionField A 3) (X (i,k)) := by
  change transposeFractionEquiv A
    (ConstantFrameElimination.leftFractionEquiv ℂ A 3 (FrameAction.contragredient a⁻¹)
      (transposeFractionEquiv A
        (algebraMap (ConstantFrameElimination.PolynomialRing A 3)
          (ConstantFrameElimination.FunctionField A 3) (X (i,j))))) = _
  rw [transposeFractionEquiv_variable,
    ConstantFrameElimination.leftFractionEquiv_polynomial,
    ConstantFrameElimination.leftSubstitution_X, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, map_mul, transposeFractionEquiv_variable]
  change transposeFractionEquiv A
      (algebraMap A (ConstantFrameElimination.FunctionField A 3)
        (algebraMap ℂ A ((FrameAction.contragredient a⁻¹).val j k))) * _ = _
  rw [(transposeFractionEquiv A).commutes]
  simp only [FrameAction.contragredient_coe, inv_inv, Matrix.transpose_apply]

/-- The literal deck transformation of the first original frame. -/
def firstDeck (a : ConstantFrameElimination.GLn ℂ 3) : PF ≃ₐ[ℂ] PF :=
  ProjectiveNoName.rationalCoefficientEquiv ℂ Index (rightFractionEquiv ℂ a)

/-- The literal deck transformation of the second original frame. -/
def secondDeck (b : ConstantFrameElimination.GLn ℂ 3) : PF ≃ₐ[ℂ] PF :=
  (rightFractionEquiv MF b).restrictScalars ℂ

/-- The genuine swap of the two original independent rational coordinate families. -/
def pairSwap : PF ≃ₐ[ℂ] PF := ProjectiveNoName.rationalVariableSwap ℂ Index Index

theorem firstDeck_firstFrame (a : ConstantFrameElimination.GLn ℂ 3) (i j : Fin 3) :
    firstDeck a (firstFrame ℂ i j) =
      (firstFrame ℂ * a.val.map (algebraMap ℂ PF)) i j := by
  change ProjectiveNoName.rationalCoefficientEquiv ℂ Index (rightFractionEquiv ℂ a)
    (algebraMap MF PF (genericFieldMatrix ℂ i j)) = _
  rw [ProjectiveNoName.rationalCoefficientEquiv_coefficient]
  change algebraMap MF PF (rightFractionEquiv ℂ a
    (algebraMap (ConstantFrameElimination.PolynomialRing ℂ 3) MF (X (i,j)))) = _
  rw [rightFractionEquiv_variable, map_sum]
  change (∑ k : Fin 3, algebraMap MF PF
    (algebraMap ℂ MF (algebraMap ℂ ℂ (a.val k j)) * genericFieldMatrix ℂ i k)) = _
  simp only [map_mul, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mul_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← IsScalarTower.algebraMap_apply ℂ MF PF]
  exact mul_comm _ _

@[simp] theorem firstDeck_secondFrame (a : ConstantFrameElimination.GLn ℂ 3) (i j : Fin 3) :
    firstDeck a (secondFrame ℂ i j) = secondFrame ℂ i j :=
  ProjectiveNoName.rationalCoefficientEquiv_variable ℂ Index (rightFractionEquiv ℂ a) (i,j)

@[simp] theorem secondDeck_firstFrame (b : ConstantFrameElimination.GLn ℂ 3) (i j : Fin 3) :
    secondDeck b (firstFrame ℂ i j) = firstFrame ℂ i j :=
  (rightFractionEquiv MF b).commutes (genericFieldMatrix ℂ i j)

theorem secondDeck_secondFrame (b : ConstantFrameElimination.GLn ℂ 3) (i j : Fin 3) :
    secondDeck b (secondFrame ℂ i j) =
      (secondFrame ℂ * b.val.map (algebraMap ℂ PF)) i j := by
  change rightFractionEquiv MF b
    (algebraMap (ConstantFrameElimination.PolynomialRing MF 3) PF (X (i,j))) = _
  rw [rightFractionEquiv_variable]
  change (∑ k : Fin 3, algebraMap MF PF (algebraMap ℂ MF (b.val k j)) *
    secondFrame ℂ i k) = _
  simp only [Matrix.mul_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← IsScalarTower.algebraMap_apply ℂ MF PF]
  exact mul_comm _ _

@[simp] theorem pairSwap_firstFrame (i j : Fin 3) :
    pairSwap (firstFrame ℂ i j) = secondFrame ℂ i j :=
  ProjectiveNoName.rationalVariableSwap_coefficient ℂ Index Index (i,j)

@[simp] theorem pairSwap_secondFrame (i j : Fin 3) :
    pairSwap (secondFrame ℂ i j) = firstFrame ℂ i j :=
  ProjectiveNoName.rationalVariableSwap_outer ℂ Index Index (i,j)

/-- The two actual independent right deck maps. -/
def pairDeck (a b : Gamma) : PF ≃ₐ[ℂ] PF :=
  firstDeck (FrameAction.tetrahedralGL a) * secondDeck (FrameAction.tetrahedralGL b)

theorem pairDeck_firstFrame (a b : Gamma) :
    (firstFrame ℂ).map (pairDeck a b).toRingHom =
      firstFrame ℂ * (FrameAction.tetrahedralGL a).val.map (algebraMap ℂ PF) := by
  ext i j
  change firstDeck (FrameAction.tetrahedralGL a)
    (secondDeck (FrameAction.tetrahedralGL b) (firstFrame ℂ i j)) = _
  rw [secondDeck_firstFrame, firstDeck_firstFrame]

theorem pairDeck_secondFrame (a b : Gamma) :
    (secondFrame ℂ).map (pairDeck a b).toRingHom =
      secondFrame ℂ * (FrameAction.tetrahedralGL b).val.map (algebraMap ℂ PF) := by
  ext i j
  change firstDeck (FrameAction.tetrahedralGL a)
    (secondDeck (FrameAction.tetrahedralGL b) (secondFrame ℂ i j)) = _
  rw [secondDeck_secondFrame]
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, firstDeck_secondFrame,
    AlgEquiv.commutes]

/-- The original right decks induce exactly the inverse native point operator on `HᵀF`. -/
theorem pairDeck_invariantMatrix (a b : Gamma) :
    (invariantMatrix ℂ).map (pairDeck a b).toRingHom =
      ((FrameAction.tetrahedralGL b)⁻¹).val.map (algebraMap ℂ PF) *
        invariantMatrix ℂ * (FrameAction.tetrahedralGL a).val.map (algebraMap ℂ PF) := by
  change ((secondFrame ℂ).transpose * firstFrame ℂ).map (pairDeck a b).toRingHom = _
  rw [Matrix.map_mul, Matrix.transpose_map, pairDeck_firstFrame, pairDeck_secondFrame,
    Matrix.transpose_mul, ← Matrix.transpose_map, FrameAction.tetrahedralGL_orthogonal]
  simp only [invariantMatrix, Matrix.mul_assoc]

/-- Swapping the original two independent frames transposes the actual invariant matrix. -/
theorem pairSwap_invariantMatrix :
    (invariantMatrix ℂ).map pairSwap.toRingHom = (invariantMatrix ℂ).transpose := by
  have hF : (firstFrame ℂ).map pairSwap.toRingHom = secondFrame ℂ := by
    ext i j
    exact pairSwap_firstFrame i j
  have hH : (secondFrame ℂ).map pairSwap.toRingHom = firstFrame ℂ := by
    ext i j
    exact pairSwap_secondFrame i j
  change ((secondFrame ℂ).transpose * firstFrame ℂ).map pairSwap.toRingHom = _
  rw [Matrix.map_mul, Matrix.transpose_map, hF, hH]
  simp only [invariantMatrix, Matrix.transpose_mul, Matrix.transpose_transpose]

end ActualDecks

section NativeCoordinates

abbrev entryIndex := ProjectiveFunctionField.matrixIndexEquiv

theorem affineIndex_native (i : Fin 8) : affineIndex i = entryIndex.symm i.castSucc := rfl

theorem pivotIndex_native : pivotIndex = entryIndex.symm (Fin.last 8) := rfl

def invariantEntry (i : Fin 9) : PF :=
  invariantMatrix ℂ (entryIndex.symm i).1 (entryIndex.symm i).2

def invariantPivot : PF := invariantEntry (Fin.last 8)

theorem invariantEntry_ne_zero (i : Fin 9) : invariantEntry i ≠ 0 := by
  have hx : genericFieldMatrix ℂ (entryIndex.symm i).1 (entryIndex.symm i).2 ≠ 0 := by
    intro h
    apply MvPolynomial.X_ne_zero (R := ℂ) (entryIndex.symm i)
    exact (IsFractionRing.injective (ConstantFrameElimination.PolynomialRing ℂ 3) MF)
      (h.trans (map_zero _).symm)
  change invariantMatrix ℂ (entryIndex.symm i).1 (entryIndex.symm i).2 ≠ 0
  rw [← invariantEmbedding_coordinate]
  intro h
  apply hx
  apply (invariantEmbedding ℂ).injective
  exact h.trans (map_zero _).symm

theorem invariantPivot_ne_zero : invariantPivot ≠ 0 := invariantEntry_ne_zero _

/-- Evaluation of the native normalized homogeneous polynomial in the original pair field. -/
def normalizedPairMap : HomogeneousRing →ₐ[ℂ] PF :=
  projectiveInvariantEmbedding.comp
    (matrixFunctionFieldEquiv.symm.toAlgHom.comp
      ((IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)).comp
        ProjectiveNoName.Concrete.normalizedPolynomialHom))

theorem normalizedPairMap_apply (p : HomogeneousRing) :
    normalizedPairMap p = projectiveInvariantEmbedding
      (matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
          (FrameProjectiveRatios.normalizedPolynomial (Fin.last 8) p))) := rfl

theorem normalizedPolynomialHom_last :
    ProjectiveNoName.Concrete.normalizedPolynomialHom (X (Fin.last 8)) = 1 := by
  change chartCoordinatesEquiv 8 (Fin.last 8)
    (ProjectiveGeometry.Dehomogenization.dehomogenize (Fin.last 8) (X (Fin.last 8))) = 1
  rw [ProjectiveGeometry.Dehomogenization.dehomogenize_X_self, map_one]

theorem normalizedPolynomialHom_castSucc (a : Fin 8) :
    ProjectiveNoName.Concrete.normalizedPolynomialHom (X a.castSucc) = X a := by
  change chartCoordinatesEquiv 8 (Fin.last 8)
    (ProjectiveGeometry.Dehomogenization.dehomogenize (Fin.last 8) (X a.castSucc)) = X a
  rw [ProjectiveGeometry.Dehomogenization.dehomogenize_X_of_ne _ _ (Fin.castSucc_ne_last a)]
  simp only [chartCoordinatesEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  congr 1
  apply (finSuccAboveEquiv (Fin.last 8)).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change a.castSucc = (Fin.last 8).succAbove a
  exact (Fin.succAbove_last_apply a).symm

theorem normalizedPairMap_X (i : Fin 9) :
    normalizedPairMap (X i) = invariantEntry i / invariantPivot := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · change projectiveInvariantEmbedding (matrixFunctionFieldEquiv.symm
      (algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
        (ProjectiveNoName.Concrete.normalizedPolynomialHom (X (Fin.last 8))))) = _
    rw [normalizedPolynomialHom_last, map_one, map_one, map_one]
    exact (div_self invariantPivot_ne_zero).symm
  · change projectiveInvariantEmbedding (matrixFunctionFieldEquiv.symm
      (algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
        (ProjectiveNoName.Concrete.normalizedPolynomialHom (X a.castSucc)))) = _
    rw [normalizedPolynomialHom_castSucc]
    have he : matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8) (X a)) =
        coordinateRatio 8 (Fin.last 8) a := by
      apply matrixFunctionFieldEquiv.injective
      rw [AlgEquiv.apply_symm_apply]
      exact (functionFieldEquiv_coordinateRatio 8 (Fin.last 8) a).symm
    rw [he, projectiveInvariantEmbedding_coordinateRatio, affineIndex_native, pivotIndex_native]
    rfl

/-- The genuine homogeneous matrix of the nine native projective coordinates. -/
def polynomialMatrix : Matrix (Fin 3) (Fin 3) HomogeneousRing :=
  fun i j => X (entryIndex (i,j))

theorem normalizedPairMap_polynomialMatrix :
    polynomialMatrix.map normalizedPairMap.toRingHom = invariantPivot⁻¹ • invariantMatrix ℂ := by
  ext i j
  change normalizedPairMap (X (entryIndex (i,j))) = _
  rw [normalizedPairMap_X]
  simp only [invariantEntry, Equiv.symm_apply_apply, Matrix.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

theorem normalizedPairMap_constantMatrix (L : Matrix (Fin 3) (Fin 3) ℂ) :
    (L.map C).map normalizedPairMap.toRingHom = L.map (algebraMap ℂ PF) := by
  ext i j
  exact normalizedPairMap.commutes (L i j)

end NativeCoordinates

section NativeOperators

theorem inverse_even_operator (a b : Gamma) (M : FrameAction.Mat3 ℂ) :
    FrameAction.tetrahedralRepresentation ((FrameAction.FrameGroup.pairHom (a,b) : W)⁻¹) M =
      ((FrameAction.tetrahedralGL b)⁻¹).val * M * (FrameAction.tetrahedralGL a).val := by
  change (FrameAction.tetrahedralGL b⁻¹).val * M *
    ((FrameAction.tetrahedralGL a⁻¹)⁻¹).val = _
  rw [map_inv, map_inv, inv_inv]

theorem inverse_tau_operator (M : FrameAction.Mat3 ℂ) :
    FrameAction.tetrahedralRepresentation ((FrameAction.FrameGroup.tau : W)⁻¹) M = M.transpose := by
  have ht : (FrameAction.FrameGroup.tau : W)⁻¹ = FrameAction.FrameGroup.tau := by
    calc
      (FrameAction.FrameGroup.tau : W)⁻¹ = FrameAction.FrameGroup.tau⁻¹ * 1 := (mul_one _).symm
      _ = FrameAction.FrameGroup.tau⁻¹ * (FrameAction.FrameGroup.tau * FrameAction.FrameGroup.tau) :=
        congrArg (fun z : W => FrameAction.FrameGroup.tau⁻¹ * z)
          FrameAction.FrameGroup.tau_squared.symm
      _ = FrameAction.FrameGroup.tau := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [ht]
  change (FrameAction.tetrahedralGL 1).val * M.transpose *
    ((FrameAction.tetrahedralGL 1)⁻¹).val = _
  simp only [map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

/-- The native homogeneous linear forms are literally the inverse even matrix operator. -/
theorem linearForms_even (a b : Gamma) (i j : Fin 3) :
    linearForms (matrixRepresentation ((FrameAction.FrameGroup.pairHom (a,b) : W)⁻¹))
        (entryIndex (i,j)) =
      (((FrameAction.tetrahedralGL b)⁻¹).val.map C * polynomialMatrix *
        (FrameAction.tetrahedralGL a).val.map C : Matrix (Fin 3) (Fin 3) HomogeneousRing) i j := by
  apply MvPolynomial.funext
  intro v
  have h := congrFun (matrixRepresentation_matrixCoordinates
    ((FrameAction.FrameGroup.pairHom (a,b) : W)⁻¹) (matrixCoordinates.symm v)) (entryIndex (i,j))
  rw [matrixCoordinates.apply_symm_apply, inverse_even_operator] at h
  simpa [linearForms, polynomialMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    matrixCoordinates, entryIndex] using h

/-- The native odd-generator forms are literally transposed original coordinates. -/
theorem linearForms_tau (i j : Fin 3) :
    linearForms (matrixRepresentation ((FrameAction.FrameGroup.tau : W)⁻¹))
        (entryIndex (i,j)) = polynomialMatrix j i := by
  apply MvPolynomial.funext
  intro v
  have h := congrFun (matrixRepresentation_matrixCoordinates
    ((FrameAction.FrameGroup.tau : W)⁻¹) (matrixCoordinates.symm v)) (entryIndex (i,j))
  rw [matrixCoordinates.apply_symm_apply, inverse_tau_operator] at h
  simpa [linearForms, polynomialMatrix, Matrix.mulVec, dotProduct, matrixCoordinates, entryIndex] using h

theorem normalizedPairMap_even_linearForms (a b : Gamma) (i j : Fin 3) :
    normalizedPairMap
      (linearForms (matrixRepresentation ((FrameAction.FrameGroup.pairHom (a,b) : W)⁻¹))
        (entryIndex (i,j))) =
      (((FrameAction.tetrahedralGL b)⁻¹).val.map (algebraMap ℂ PF) * invariantMatrix ℂ *
        (FrameAction.tetrahedralGL a).val.map (algebraMap ℂ PF)) i j / invariantPivot := by
  rw [linearForms_even]
  change (((((FrameAction.tetrahedralGL b)⁻¹).val.map C * polynomialMatrix *
    (FrameAction.tetrahedralGL a).val.map C).map normalizedPairMap.toRingHom) i j) = _
  rw [Matrix.map_mul, Matrix.map_mul, normalizedPairMap_constantMatrix,
    normalizedPairMap_constantMatrix, normalizedPairMap_polynomialMatrix]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

theorem normalizedPairMap_tau_linearForms (i j : Fin 3) :
    normalizedPairMap
      (linearForms (matrixRepresentation ((FrameAction.FrameGroup.tau : W)⁻¹))
        (entryIndex (i,j))) = invariantMatrix ℂ j i / invariantPivot := by
  rw [linearForms_tau]
  change normalizedPairMap (X (entryIndex (j,i))) = _
  rw [normalizedPairMap_X]
  simp only [invariantEntry, Equiv.symm_apply_apply]

/-- Native inverse pullback, embedded in the original pair field, on an actual chart ratio. -/
theorem embedded_fieldRepresentation_coordinateRatio (w : W) (i : Fin 8) :
    projectiveInvariantEmbedding (fieldRepresentation w (coordinateRatio 8 (Fin.last 8) i)) =
      normalizedPairMap (linearForms (matrixRepresentation w⁻¹) i.castSucc) /
        normalizedPairMap (linearForms (matrixRepresentation w⁻¹) (Fin.last 8)) := by
  have h : fieldRepresentation w (coordinateRatio 8 (Fin.last 8) i) =
      matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
          (FrameProjectiveRatios.normalizedPolynomial (Fin.last 8)
            (linearForms (matrixRepresentation w⁻¹) i.castSucc)) /
        algebraMap (MvPolynomial (Fin 8) ℂ) (RationalField ℂ 8)
          (FrameProjectiveRatios.normalizedPolynomial (Fin.last 8)
            (linearForms (matrixRepresentation w⁻¹) (Fin.last 8)))) := by
    apply matrixFunctionFieldEquiv.injective
    rw [AlgEquiv.apply_symm_apply]
    change functionFieldEquiv 8 (Fin.last 8)
      (fieldRepresentation w (coordinateRatio 8 (Fin.last 8) i)) = _
    simpa only [finSuccAboveEquiv_apply, Fin.succAbove_last] using
      FrameProjectiveRatios.functionFieldEquiv_fieldRepresentation_coordinateRatio w (Fin.last 8) i
  rw [h, map_div₀, map_div₀]
  rfl

end NativeOperators

section Equivariance

theorem pairDeck_coordinateRatio (a b : Gamma) (i : Fin 8) :
    pairDeck a b (projectiveInvariantEmbedding (coordinateRatio 8 (Fin.last 8) i)) =
      projectiveInvariantEmbedding
        (fieldRepresentation (FrameAction.FrameGroup.pairHom (a,b))
          (coordinateRatio 8 (Fin.last 8) i)) := by
  let Z : Matrix (Fin 3) (Fin 3) PF :=
    ((FrameAction.tetrahedralGL b)⁻¹).val.map (algebraMap ℂ PF) * invariantMatrix ℂ *
      (FrameAction.tetrahedralGL a).val.map (algebraMap ℂ PF)
  have hn (k : Fin 9) :
      normalizedPairMap
        (linearForms (matrixRepresentation ((FrameAction.FrameGroup.pairHom (a,b) : W)⁻¹)) k) =
        Z (entryIndex.symm k).1 (entryIndex.symm k).2 / invariantPivot := by
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using
      normalizedPairMap_even_linearForms a b (entryIndex.symm k).1 (entryIndex.symm k).2
  rw [projectiveInvariantEmbedding_coordinateRatio,
    embedded_fieldRepresentation_coordinateRatio, hn, hn, map_div₀]
  have hz (u v : Fin 3) : pairDeck a b (invariantMatrix ℂ u v) = Z u v :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) PF => M u v) (pairDeck_invariantMatrix a b)
  rw [hz, hz]
  change Z (affineIndex i).1 (affineIndex i).2 / Z pivotIndex.1 pivotIndex.2 =
    (Z (affineIndex i).1 (affineIndex i).2 / invariantPivot) /
      (Z pivotIndex.1 pivotIndex.2 / invariantPivot)
  exact (div_div_div_cancel_right₀ invariantPivot_ne_zero _ _).symm

theorem pairSwap_coordinateRatio (i : Fin 8) :
    pairSwap (projectiveInvariantEmbedding (coordinateRatio 8 (Fin.last 8) i)) =
      projectiveInvariantEmbedding
        (fieldRepresentation FrameAction.FrameGroup.tau (coordinateRatio 8 (Fin.last 8) i)) := by
  have hn (k : Fin 9) :
      normalizedPairMap
        (linearForms (matrixRepresentation ((FrameAction.FrameGroup.tau : W)⁻¹)) k) =
        invariantMatrix ℂ (entryIndex.symm k).2 (entryIndex.symm k).1 / invariantPivot := by
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using
      normalizedPairMap_tau_linearForms (entryIndex.symm k).1 (entryIndex.symm k).2
  rw [projectiveInvariantEmbedding_coordinateRatio,
    embedded_fieldRepresentation_coordinateRatio, hn, hn, map_div₀]
  have hs (u v : Fin 3) : pairSwap (invariantMatrix ℂ u v) = invariantMatrix ℂ v u :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) PF => M u v) pairSwap_invariantMatrix
  rw [hs, hs]
  change invariantMatrix ℂ (affineIndex i).2 (affineIndex i).1 /
      invariantMatrix ℂ pivotIndex.2 pivotIndex.1 =
    (invariantMatrix ℂ (affineIndex i).2 (affineIndex i).1 / invariantPivot) /
      (invariantMatrix ℂ pivotIndex.2 pivotIndex.1 / invariantPivot)
  exact (div_div_div_cancel_right₀ invariantPivot_ne_zero _ _).symm

/-- All native rational functions, rather than just matrix-coordinate ratios, transform
by the literal original right-frame decks. -/
theorem pairDeck_embedding (a b : Gamma) (f : NativeMatrixField) :
    pairDeck a b (projectiveInvariantEmbedding f) =
      projectiveInvariantEmbedding
        (fieldRepresentation (FrameAction.FrameGroup.pairHom (a,b)) f) := by
  have h : (pairDeck a b).toRingHom.comp projectiveInvariantEmbedding.toRingHom =
      projectiveInvariantEmbedding.toRingHom.comp
        (fieldRepresentation (FrameAction.FrameGroup.pairHom (a,b))).toRingHom := by
    apply ProjectiveNoName.Concrete.nativeRingHom_ext
    · intro c
      change pairDeck a b (projectiveInvariantEmbedding (algebraMap ℂ NativeMatrixField c)) =
        projectiveInvariantEmbedding
          (fieldRepresentation (FrameAction.FrameGroup.pairHom (a,b))
            (algebraMap ℂ NativeMatrixField c))
      simp only [AlgHom.commutes, AlgEquiv.commutes]
    · exact pairDeck_coordinateRatio a b
  exact RingHom.congr_fun h f

/-- The original variable-family swap induces native transposition on the entire field. -/
theorem pairSwap_embedding (f : NativeMatrixField) :
    pairSwap (projectiveInvariantEmbedding f) =
      projectiveInvariantEmbedding (fieldRepresentation FrameAction.FrameGroup.tau f) := by
  have h : pairSwap.toRingHom.comp projectiveInvariantEmbedding.toRingHom =
      projectiveInvariantEmbedding.toRingHom.comp
        (fieldRepresentation FrameAction.FrameGroup.tau).toRingHom := by
    apply ProjectiveNoName.Concrete.nativeRingHom_ext
    · intro c
      change pairSwap (projectiveInvariantEmbedding (algebraMap ℂ NativeMatrixField c)) =
        projectiveInvariantEmbedding
          (fieldRepresentation FrameAction.FrameGroup.tau (algebraMap ℂ NativeMatrixField c))
      simp only [AlgHom.commutes, AlgEquiv.commutes]
    · exact pairSwap_coordinateRatio
  exact RingHom.congr_fun h f

/-- A genuine original pair-field automorphism for each wreath normal form. -/
def deckOperator (w : W) : PF ≃ₐ[ℂ] PF :=
  pairDeck w.first w.second * if w.odd then pairSwap else 1

theorem deckOperator_even (a b : Gamma) :
    deckOperator (FrameAction.FrameGroup.pairHom (a,b)) = pairDeck a b := by
  change pairDeck a b * (if false then pairSwap else 1) = _
  simp only [Bool.false_eq_true, ite_false, mul_one]

theorem deckOperator_embedding (w : W) (f : NativeMatrixField) :
    deckOperator w (projectiveInvariantEmbedding f) =
      projectiveInvariantEmbedding (fieldRepresentation w f) := by
  rcases w with ⟨a,b,o⟩
  cases o
  · change (pairDeck a b * 1) (projectiveInvariantEmbedding f) = _
    rw [mul_one]
    exact pairDeck_embedding a b f
  · have hw : (⟨a,b,true⟩ : W) =
        FrameAction.FrameGroup.pairHom (a,b) * FrameAction.FrameGroup.tau := by
      change (⟨a,b,true⟩ : W) = ⟨a * 1,b * 1,true⟩
      simp only [mul_one]
    change pairDeck a b (pairSwap (projectiveInvariantEmbedding f)) = _
    rw [pairSwap_embedding, pairDeck_embedding, hw, map_mul]
    rfl

end Equivariance

section ActualRestriction

/-- Restrict an actual ambient automorphism, using preservation in both directions. -/
def restrictFieldEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (T : IntermediateField K L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ x ∈ T, σ x ∈ T) (hσi : ∀ x ∈ T, σ.symm x ∈ T) : T ≃ₐ[K] T where
  toFun x := ⟨σ x.val, hσ x.val x.property⟩
  invFun x := ⟨σ.symm x.val, hσi x.val x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.val)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (map_mul σ x.val y.val)
  map_add' x y := Subtype.ext (map_add σ x.val y.val)
  commutes' c := Subtype.ext (σ.commutes c)

theorem deckOperator_symm_embedding (w : W) (f : NativeMatrixField) :
    (deckOperator w).symm (projectiveInvariantEmbedding f) =
      projectiveInvariantEmbedding ((fieldRepresentation w).symm f) := by
  apply (deckOperator w).injective
  rw [AlgEquiv.apply_symm_apply, deckOperator_embedding, AlgEquiv.apply_symm_apply]

theorem deckOperator_connected_mem (w : W) (x : PF) (hx : x ∈ projectiveConnectedField) :
    deckOperator w x ∈ projectiveConnectedField := by
  obtain ⟨f,rfl⟩ := (projective_connected_invariant_iff x).mp hx
  rw [deckOperator_embedding]
  exact (projective_connected_invariant_iff _).mpr ⟨fieldRepresentation w f,rfl⟩

theorem deckOperator_symm_connected_mem (w : W) (x : PF)
    (hx : x ∈ projectiveConnectedField) :
    (deckOperator w).symm x ∈ projectiveConnectedField := by
  obtain ⟨f,rfl⟩ := (projective_connected_invariant_iff x).mp hx
  rw [deckOperator_symm_embedding]
  exact (projective_connected_invariant_iff _).mpr ⟨(fieldRepresentation w).symm f,rfl⟩

/-- The literal restriction of the original deck, with its actual ambient values. -/
def connectedDeckEquiv (w : W) : projectiveConnectedField ≃ₐ[ℂ] projectiveConnectedField :=
  restrictFieldEquiv projectiveConnectedField (deckOperator w)
    (deckOperator_connected_mem w) (deckOperator_symm_connected_mem w)

/-- The same actual deck action on the proved native PGL-invariant subfield. -/
def pglDeckEquiv (w : W) :
    ProjectiveFrameAction.pglFixedField ≃ₐ[ℂ] ProjectiveFrameAction.pglFixedField :=
  ProjectiveFrameAction.pglFixedEquiv.trans
    ((connectedDeckEquiv w).trans ProjectiveFrameAction.pglFixedEquiv.symm)

/-- The literal double inclusion of the original projective pair's PGL-fixed field. -/
def pglAmbientEmbedding : ProjectiveFrameAction.pglFixedField →ₐ[ℂ] PF :=
  projectivePairField.val.comp ProjectiveFrameAction.pglFixedField.val

theorem pglAmbientEmbedding_native (f : NativeMatrixField) :
    pglAmbientEmbedding (ProjectiveFrameAction.nativePGLQuotientEquiv f) =
      projectiveInvariantEmbedding f := rfl

theorem pglAmbientEmbedding_deck (w : W) (x : ProjectiveFrameAction.pglFixedField) :
    pglAmbientEmbedding (pglDeckEquiv w x) = deckOperator w (pglAmbientEmbedding x) := rfl

theorem nativePGLQuotientEquiv_symm_embedding (x : ProjectiveFrameAction.pglFixedField) :
    projectiveInvariantEmbedding (ProjectiveFrameAction.nativePGLQuotientEquiv.symm x) =
      pglAmbientEmbedding x := by
  have h := pglAmbientEmbedding_native (ProjectiveFrameAction.nativePGLQuotientEquiv.symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- The induced native automorphism is obtained by actual restriction and the
proved native connected quotient equivalence. -/
def inducedNative (w : W) : NativeMatrixField ≃ₐ[ℂ] NativeMatrixField :=
  ProjectiveFrameAction.nativePGLQuotientEquiv.trans
    ((pglDeckEquiv w).trans ProjectiveFrameAction.nativePGLQuotientEquiv.symm)

theorem inducedNative_embedding (w : W) (f : NativeMatrixField) :
    projectiveInvariantEmbedding (inducedNative w f) =
      deckOperator w (projectiveInvariantEmbedding f) := by
  change projectiveInvariantEmbedding
    (ProjectiveFrameAction.nativePGLQuotientEquiv.symm
      (pglDeckEquiv w (ProjectiveFrameAction.nativePGLQuotientEquiv f))) = _
  rw [nativePGLQuotientEquiv_symm_embedding, pglAmbientEmbedding_deck,
    pglAmbientEmbedding_native]

/-- The native field action is exactly the one induced by the original frame decks. -/
theorem inducedNative_eq_fieldRepresentation (w : W) :
    inducedNative w = fieldRepresentation w := by
  apply AlgEquiv.ext
  intro f
  apply projectiveInvariantEmbedding.injective
  change projectiveInvariantEmbedding (inducedNative w f) =
    projectiveInvariantEmbedding (fieldRepresentation w f)
  rw [inducedNative_embedding, deckOperator_embedding]

/-- The actual induced native automorphisms form the wreath-group action. -/
def inducedRepresentation : W →* (NativeMatrixField ≃ₐ[ℂ] NativeMatrixField) where
  toFun := inducedNative
  map_one' := by rw [inducedNative_eq_fieldRepresentation, map_one]
  map_mul' w v := by
    rw [inducedNative_eq_fieldRepresentation, inducedNative_eq_fieldRepresentation,
      inducedNative_eq_fieldRepresentation, map_mul]

theorem inducedRepresentation_eq : inducedRepresentation = fieldRepresentation := by
  ext w f
  exact AlgEquiv.congr_fun (inducedNative_eq_fieldRepresentation w) f

/-- Equivariance through the actual PGL quotient, before forgetting either inclusion. -/
theorem nativePGLQuotientEquiv_equivariant (w : W) (f : NativeMatrixField) :
    pglDeckEquiv w (ProjectiveFrameAction.nativePGLQuotientEquiv f) =
      ProjectiveFrameAction.nativePGLQuotientEquiv (fieldRepresentation w f) := by
  apply pglAmbientEmbedding.injective
  change pglAmbientEmbedding
      (pglDeckEquiv w (ProjectiveFrameAction.nativePGLQuotientEquiv f)) =
    pglAmbientEmbedding
      (ProjectiveFrameAction.nativePGLQuotientEquiv (fieldRepresentation w f))
  rw [pglAmbientEmbedding_deck, pglAmbientEmbedding_native, pglAmbientEmbedding_native,
    deckOperator_embedding]

/-- The action on actual PGL invariants is itself a genuine group action. -/
def pglDeckRepresentation : W →*
    (ProjectiveFrameAction.pglFixedField ≃ₐ[ℂ] ProjectiveFrameAction.pglFixedField) where
  toFun := pglDeckEquiv
  map_one' := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨f,rfl⟩ := ProjectiveFrameAction.nativePGLQuotientEquiv.surjective x
    rw [nativePGLQuotientEquiv_equivariant, map_one]
    rfl
  map_mul' w v := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨f,rfl⟩ := ProjectiveFrameAction.nativePGLQuotientEquiv.surjective x
    change pglDeckEquiv (w * v) (ProjectiveFrameAction.nativePGLQuotientEquiv f) =
      pglDeckEquiv w (pglDeckEquiv v (ProjectiveFrameAction.nativePGLQuotientEquiv f))
    rw [nativePGLQuotientEquiv_equivariant, nativePGLQuotientEquiv_equivariant,
      nativePGLQuotientEquiv_equivariant, map_mul]
    rfl

end ActualRestriction

section GeneratorFormulas

/-- Explicit native projective-coordinate formula for the even original deck. -/
theorem native_even_coordinateRatio (a b : Gamma) (i : Fin 8) :
    projectiveInvariantEmbedding
      (fieldRepresentation (FrameAction.FrameGroup.pairHom (a,b))
        (coordinateRatio 8 (Fin.last 8) i)) =
    (((FrameAction.tetrahedralGL b)⁻¹).val.map (algebraMap ℂ PF) * invariantMatrix ℂ *
      (FrameAction.tetrahedralGL a).val.map (algebraMap ℂ PF))
        (affineIndex i).1 (affineIndex i).2 /
    (((FrameAction.tetrahedralGL b)⁻¹).val.map (algebraMap ℂ PF) * invariantMatrix ℂ *
      (FrameAction.tetrahedralGL a).val.map (algebraMap ℂ PF)) pivotIndex.1 pivotIndex.2 := by
  rw [← pairDeck_coordinateRatio, projectiveInvariantEmbedding_coordinateRatio, map_div₀]
  exact congrArg₂ (fun x y : PF => x / y)
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) PF => M (affineIndex i).1 (affineIndex i).2)
      (pairDeck_invariantMatrix a b))
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) PF => M pivotIndex.1 pivotIndex.2)
      (pairDeck_invariantMatrix a b))

/-- Explicit native projective-coordinate formula for the original family swap. -/
theorem native_tau_coordinateRatio (i : Fin 8) :
    projectiveInvariantEmbedding
      (fieldRepresentation FrameAction.FrameGroup.tau (coordinateRatio 8 (Fin.last 8) i)) =
    invariantMatrix ℂ (affineIndex i).2 (affineIndex i).1 /
      invariantMatrix ℂ pivotIndex.2 pivotIndex.1 := by
  rw [← pairSwap_coordinateRatio, projectiveInvariantEmbedding_coordinateRatio, map_div₀]
  exact congrArg₂ (fun x y : PF => x / y)
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) PF => M (affineIndex i).1 (affineIndex i).2)
      pairSwap_invariantMatrix)
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) PF => M pivotIndex.1 pivotIndex.2)
      pairSwap_invariantMatrix)

end GeneratorFormulas

end M9.FrameQuotientActionComparison

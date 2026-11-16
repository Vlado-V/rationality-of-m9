module

public import M9StacksIntegration.ConicFramePairFieldComparison
public import M9StacksIntegration.ConicFrameIndependentPairAction
public import M9StacksIntegration.ConicFrameFixedField

/-! The actual product conic-cover pullback and the independent right
tetrahedral fixed field, with the original named chart coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

open scoped TensorProduct
open MvPolynomial

namespace M9Native.ConicFramePairFixedField

open ConicFramePairRings ConicFrameSourceAlgebra

abbrev Gamma := ConicFrameGammaAction.Gamma
abbrev OneField := ConicFrameIndependentPairAction.OneField
abbrev PairField := ConicFrameIndependentPairAction.PairField
abbrev SourceField := sourcePairField ℂ
abbrev P := ConicFrameProjective.polynomial ℂ

/-- The exact independent-variable fraction comparison. The first tensor
factor becomes coefficients and the second becomes the outer variables. -/
def sourceToNested : SourceField ≃ₐ[ℂ] PairField :=
  (sourcePairRationalEquiv ℂ).trans
    ((M9.rationalFieldReindex ℂ (Equiv.sumComm (Fin 8) (Fin 8))).trans
      (M9.rationalFieldSumVariables ℂ (Fin 8) (Fin 8)).symm)

theorem sourceToNested_polynomialPair (p : polynomialPair ℂ) :
    M9.rationalFieldSumVariables ℂ (Fin 8) (Fin 8)
      (sourceToNested (algebraMap (sourcePair ℂ) SourceField
        (algebraMap (polynomialPair ℂ) (sourcePair ℂ) p))) =
      algebraMap (MvPolynomial (Fin 8 ⊕ Fin 8) ℂ)
        (FractionRing (MvPolynomial (Fin 8 ⊕ Fin 8) ℂ))
        (MvPolynomial.rename (Equiv.sumComm (Fin 8) (Fin 8)) (polynomialPairEquiv ℂ p)) := by
  simp only [sourceToNested, sourcePairRationalEquiv, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply, sourcePairFractionEquiv_algebraMap,
    sourcePairToPolynomialFraction_algebraMap, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    M9.rationalFieldReindex_algebraMap]

def leftSourceEmbedding : sourceRing ℂ →ₐ[ℂ] SourceField :=
  (IsScalarTower.toAlgHom ℂ (sourcePair ℂ) SourceField).comp
    (Algebra.TensorProduct.includeLeft : sourceRing ℂ →ₐ[ℂ] sourcePair ℂ)

def rightSourceEmbedding : sourceRing ℂ →ₐ[ℂ] SourceField :=
  (IsScalarTower.toAlgHom ℂ (sourcePair ℂ) SourceField).comp
    (Algebra.TensorProduct.includeRight : sourceRing ℂ →ₐ[ℂ] sourcePair ℂ)

theorem leftSourceEmbedding_injective : Function.Injective leftSourceEmbedding := by
  intro x y h
  change algebraMap (sourcePair ℂ) SourceField (x ⊗ₜ[ℂ] 1) =
    algebraMap (sourcePair ℂ) SourceField (y ⊗ₜ[ℂ] 1) at h
  have hh := (IsFractionRing.injective (sourcePair ℂ) SourceField) h
  have ht := congrArg (Algebra.TensorProduct.lmul' ℂ (S := sourceRing ℂ)) hh
  simpa only [Algebra.TensorProduct.lmul'_apply_tmul, mul_one] using ht

theorem rightSourceEmbedding_injective : Function.Injective rightSourceEmbedding := by
  intro x y h
  change algebraMap (sourcePair ℂ) SourceField (1 ⊗ₜ[ℂ] x) =
    algebraMap (sourcePair ℂ) SourceField (1 ⊗ₜ[ℂ] y) at h
  have hh := (IsFractionRing.injective (sourcePair ℂ) SourceField) h
  have ht := congrArg (Algebra.TensorProduct.lmul' ℂ (S := sourceRing ℂ)) hh
  simpa only [Algebra.TensorProduct.lmul'_apply_tmul, one_mul] using ht

def leftPolynomialEmbedding : P →ₐ[ℂ] SourceField :=
  leftSourceEmbedding.comp (polynomialToSource ℂ)

def rightPolynomialEmbedding : P →ₐ[ℂ] SourceField :=
  rightSourceEmbedding.comp (polynomialToSource ℂ)

theorem polynomialToSource_injective : Function.Injective (polynomialToSource ℂ) :=
  IsLocalization.injective (sourceRing ℂ)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (localizer_ne_zero ℂ))

theorem leftPolynomialEmbedding_injective : Function.Injective leftPolynomialEmbedding :=
  leftSourceEmbedding_injective.comp polynomialToSource_injective

theorem rightPolynomialEmbedding_injective : Function.Injective rightPolynomialEmbedding :=
  rightSourceEmbedding_injective.comp polynomialToSource_injective

def leftFieldEmbedding : OneField →ₐ[ℂ] SourceField :=
  IsFractionRing.liftAlgHom (g := leftPolynomialEmbedding) leftPolynomialEmbedding_injective

def rightFieldEmbedding : OneField →ₐ[ℂ] SourceField :=
  IsFractionRing.liftAlgHom (g := rightPolynomialEmbedding) rightPolynomialEmbedding_injective

@[simp] theorem leftFieldEmbedding_polynomial (p : P) :
    leftFieldEmbedding (algebraMap P OneField p) = leftPolynomialEmbedding p :=
  IsFractionRing.lift_algebraMap (g := leftPolynomialEmbedding.toRingHom)
    leftPolynomialEmbedding_injective p

@[simp] theorem rightFieldEmbedding_polynomial (p : P) :
    rightFieldEmbedding (algebraMap P OneField p) = rightPolynomialEmbedding p :=
  IsFractionRing.lift_algebraMap (g := rightPolynomialEmbedding.toRingHom)
    rightPolynomialEmbedding_injective p

theorem sourceToNested_leftVariable (i : Fin 8) :
    sourceToNested (leftPolynomialEmbedding (X i)) =
      ConicFrameIndependentPairAction.coefficientEmbedding
        (ConicFrameIndependentPairAction.oneVariable i) := by
  apply (M9.rationalFieldSumVariables ℂ (Fin 8) (Fin 8)).injective
  have he : leftPolynomialEmbedding (X i) =
      algebraMap (sourcePair ℂ) SourceField
        (algebraMap (polynomialPair ℂ) (sourcePair ℂ) ((X i : P) ⊗ₜ[ℂ] 1)) := by
    change algebraMap (sourcePair ℂ) SourceField ((polynomialToSource ℂ (X i)) ⊗ₜ[ℂ] 1) = _
    change algebraMap (sourcePair ℂ) SourceField ((polynomialToSource ℂ (X i)) ⊗ₜ[ℂ] 1) =
      algebraMap (sourcePair ℂ) SourceField
        (polynomialPairToSourcePair ℂ ((X i : P) ⊗ₜ[ℂ] 1))
    rw [polynomialPairToSourcePair, Algebra.TensorProduct.map_tmul, map_one]
  rw [he, sourceToNested_polynomialPair, polynomialPairEquiv,
    MvPolynomial.tensorEquivSum_X_tmul_one, MvPolynomial.rename_X]
  change _ = M9.rationalFieldSumVariables ℂ (Fin 8) (Fin 8)
    (algebraMap OneField PairField (algebraMap P OneField (X i)))
  rw [M9.ProjectiveNoName.sumVariables_coefficient]
  rfl

theorem sourceToNested_rightVariable (i : Fin 8) :
    sourceToNested (rightPolynomialEmbedding (X i)) =
      ConicFrameIndependentPairAction.outerEmbedding
        (ConicFrameIndependentPairAction.oneVariable i) := by
  apply (M9.rationalFieldSumVariables ℂ (Fin 8) (Fin 8)).injective
  have he : rightPolynomialEmbedding (X i) =
      algebraMap (sourcePair ℂ) SourceField
        (algebraMap (polynomialPair ℂ) (sourcePair ℂ) ((1 : P) ⊗ₜ[ℂ] X i)) := by
    change algebraMap (sourcePair ℂ) SourceField (1 ⊗ₜ[ℂ] polynomialToSource ℂ (X i)) = _
    change algebraMap (sourcePair ℂ) SourceField (1 ⊗ₜ[ℂ] polynomialToSource ℂ (X i)) =
      algebraMap (sourcePair ℂ) SourceField
        (polynomialPairToSourcePair ℂ ((1 : P) ⊗ₜ[ℂ] X i))
    rw [polynomialPairToSourcePair, Algebra.TensorProduct.map_tmul, map_one]
  rw [he, sourceToNested_polynomialPair, polynomialPairEquiv,
    MvPolynomial.tensorEquivSum_one_tmul_X, MvPolynomial.rename_X,
    ConicFrameIndependentPairAction.outerEmbedding_variable]
  exact (M9.ProjectiveNoName.sumVariables_outer ℂ (Fin 8) (Fin 8) i).symm

theorem sourceToNested_leftField (x : OneField) :
    sourceToNested (leftFieldEmbedding x) =
      ConicFrameIndependentPairAction.coefficientEmbedding x := by
  have h : sourceToNested.toRingHom.comp leftFieldEmbedding.toRingHom =
      ConicFrameIndependentPairAction.coefficientEmbedding.toRingHom := by
    apply M9.ProjectiveNoName.rationalRingHom_ext ℂ (Fin 8)
    · intro c
      change sourceToNested (leftFieldEmbedding (algebraMap ℂ OneField c)) = _
      rw [leftFieldEmbedding.commutes, sourceToNested.commutes]
      exact (ConicFrameIndependentPairAction.coefficientEmbedding.commutes c).symm
    · intro i
      change sourceToNested (leftFieldEmbedding (algebraMap P OneField (X i))) = _
      rw [leftFieldEmbedding_polynomial]
      exact sourceToNested_leftVariable i
  exact DFunLike.congr_fun h x

theorem sourceToNested_rightField (x : OneField) :
    sourceToNested (rightFieldEmbedding x) =
      ConicFrameIndependentPairAction.outerEmbedding x := by
  have h : sourceToNested.toRingHom.comp rightFieldEmbedding.toRingHom =
      ConicFrameIndependentPairAction.outerEmbedding.toRingHom := by
    apply M9.ProjectiveNoName.rationalRingHom_ext ℂ (Fin 8)
    · intro c
      change sourceToNested (rightFieldEmbedding (algebraMap ℂ OneField c)) = _
      rw [rightFieldEmbedding.commutes, sourceToNested.commutes]
      exact (ConicFrameIndependentPairAction.outerEmbedding.commutes c).symm
    · intro i
      change sourceToNested (rightFieldEmbedding (algebraMap P OneField (X i))) = _
      rw [rightFieldEmbedding_polynomial]
      exact sourceToNested_rightVariable i
  exact DFunLike.congr_fun h x

theorem leftFieldEmbedding_toRational (b : sourceRing ℂ) :
    leftFieldEmbedding (toRationalAlgHom ℂ b) = leftSourceEmbedding b := by
  have h : leftFieldEmbedding.toRingHom.comp (toRationalAlgHom ℂ).toRingHom =
      leftSourceEmbedding.toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (localizer ℂ))
    apply RingHom.ext
    intro p
    change leftFieldEmbedding (toRational ℂ (algebraMap P (sourceRing ℂ) p)) =
      leftSourceEmbedding (algebraMap P (sourceRing ℂ) p)
    rw [toRational_algebraMap, leftFieldEmbedding_polynomial]
    rfl
  exact DFunLike.congr_fun h b

theorem rightFieldEmbedding_toRational (b : sourceRing ℂ) :
    rightFieldEmbedding (toRationalAlgHom ℂ b) = rightSourceEmbedding b := by
  have h : rightFieldEmbedding.toRingHom.comp (toRationalAlgHom ℂ).toRingHom =
      rightSourceEmbedding.toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (localizer ℂ))
    apply RingHom.ext
    intro p
    change rightFieldEmbedding (toRational ℂ (algebraMap P (sourceRing ℂ) p)) =
      rightSourceEmbedding (algebraMap P (sourceRing ℂ) p)
    rw [toRational_algebraMap, rightFieldEmbedding_polynomial]
    rfl
  exact DFunLike.congr_fun h b

theorem sourceToNested_tmul (b c : sourceRing ℂ) :
    sourceToNested (algebraMap (sourcePair ℂ) SourceField (b ⊗ₜ[ℂ] c)) =
      ConicFrameIndependentPairAction.coefficientEmbedding (toRationalAlgHom ℂ b) *
        ConicFrameIndependentPairAction.outerEmbedding (toRationalAlgHom ℂ c) := by
  have h : algebraMap (sourcePair ℂ) SourceField (b ⊗ₜ[ℂ] c) =
      leftSourceEmbedding b * rightSourceEmbedding c := by
    change algebraMap (sourcePair ℂ) SourceField (b ⊗ₜ[ℂ] c) =
      algebraMap (sourcePair ℂ) SourceField (b ⊗ₜ[ℂ] 1) *
        algebraMap (sourcePair ℂ) SourceField (1 ⊗ₜ[ℂ] c)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, ← leftFieldEmbedding_toRational, ← rightFieldEmbedding_toRational,
    sourceToNested_leftField, sourceToNested_rightField]

def coordinateEmbedding : targetPairField ℂ →ₐ[ℂ] PairField :=
  sourceToNested.toAlgHom.comp (pairFieldEmbedding ℂ)

theorem coordinateEmbedding_tmul (a b : targetRing ℂ) :
    coordinateEmbedding (algebraMap (targetPair ℂ) (targetPairField ℂ) (a ⊗ₜ[ℂ] b)) =
      ConicFrameIndependentPairAction.coefficientEmbedding
          (toRationalAlgHom ℂ (coordinateMap ℂ a)) *
        ConicFrameIndependentPairAction.outerEmbedding
          (toRationalAlgHom ℂ (coordinateMap ℂ b)) := by
  change sourceToNested (pairFieldEmbedding ℂ _) = _
  rw [pairFieldEmbedding_algebraMap]
  change sourceToNested (algebraMap (sourcePair ℂ) SourceField
    (coordinateMap ℂ a ⊗ₜ[ℂ] coordinateMap ℂ b)) = _
  exact sourceToNested_tmul _ _

theorem coordinateValue_fixed (g : Gamma) (a : targetRing ℂ) :
    ConicFrameIndependentPairAction.oneRepresentation g
      (toRationalAlgHom ℂ (coordinateMap ℂ a)) =
        toRationalAlgHom ℂ (coordinateMap ℂ a) := by
  have h := ConicFrameGammaInvariant.targetFieldEmbedding_fixed g
    (algebraMap (targetRing ℂ) (ConicFrameExtension.targetField ℂ) a)
  rw [ConicFrameExtension.targetFieldEmbedding_algebraMap] at h
  exact h

theorem coordinateEmbedding_fixed (g : Gamma × Gamma) (z : targetPairField ℂ) :
    ConicFrameIndependentPairAction.pairRepresentation g (coordinateEmbedding z) =
      coordinateEmbedding z := by
  have h : (ConicFrameIndependentPairAction.pairRepresentation g).toRingHom.comp
      coordinateEmbedding.toRingHom = coordinateEmbedding.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := targetPair ℂ)
    intro a
    change ConicFrameIndependentPairAction.pairRepresentation g
      (coordinateEmbedding (algebraMap (targetPair ℂ) (targetPairField ℂ) a)) =
        coordinateEmbedding (algebraMap (targetPair ℂ) (targetPairField ℂ) a)
    induction a using TensorProduct.inductionOn with
    | tmul a b =>
      rw [coordinateEmbedding_tmul, map_mul,
        ConicFrameIndependentPairAction.pairRepresentation_coefficient,
        ConicFrameIndependentPairAction.pairRepresentation_outer,
        coordinateValue_fixed, coordinateValue_fixed]
    | add a b ha hb => simp only [map_add, ha, hb]
  exact DFunLike.congr_fun h z

abbrev grassmannianPairField := ConicFramePairFieldComparison.target.functionField

/-- The embedding of the actual native product-Grassmannian generic stalk
through the actual conic map and the named independent frame coordinates. -/
def functionFieldEmbedding : grassmannianPairField →ₐ[ℂ] PairField :=
  sourceToNested.toAlgHom.comp ConicFramePairFieldComparison.functionFieldEmbedding

theorem embedding_comparison (z : grassmannianPairField) :
    sourceToNested (ConicFramePairFieldComparison.sourceNativeEquiv
      (NativeDominantFunctionField.map ConicFramePairFieldComparison.conicPairMap z)) =
        functionFieldEmbedding z :=
  congrArg sourceToNested (ConicFramePairFieldComparison.embedding_comparison z)

theorem embedding_fixed (g : Gamma × Gamma) (z : grassmannianPairField) :
    ConicFrameIndependentPairAction.pairRepresentation g (functionFieldEmbedding z) =
      functionFieldEmbedding z :=
  coordinateEmbedding_fixed g (ConicFramePairFieldComparison.targetNativeEquiv z)

local instance pairAction : MulSemiringAction (Gamma × Gamma) PairField :=
  ConicFrameIndependentPairAction.pairAction

def fixedField : IntermediateField ℂ PairField where
  __ := FixedPoints.subfield (Gamma × Gamma) PairField
  algebraMap_mem' c g := (ConicFrameIndependentPairAction.pairRepresentation g).commutes c

def imageField : IntermediateField ℂ PairField := functionFieldEmbedding.fieldRange

theorem image_le_fixed : imageField ≤ fixedField := by
  rintro x ⟨z,rfl⟩ g
  exact embedding_fixed g z

/-- The image degree is transported from the actual tensor cover's proved
576-point fibres, with the exact native chart and fraction maps. -/
theorem image_finrank : Module.finrank imageField PairField = 576 := by
  let := ConicFramePairDegree.actualFieldAlgebra
  have h := Algebra.finrank_eq_of_equiv_equiv
    ((ConicFramePairFieldComparison.targetNativeEquiv.symm).trans
      functionFieldEmbedding.equivFieldRange).toRingEquiv
    sourceToNested.toRingEquiv (by
      apply RingHom.ext
      intro z
      change functionFieldEmbedding (ConicFramePairFieldComparison.targetNativeEquiv.symm z) =
        sourceToNested (pairFieldEmbedding ℂ z)
      change sourceToNested (pairFieldEmbedding ℂ
        (ConicFramePairFieldComparison.targetNativeEquiv
          (ConicFramePairFieldComparison.targetNativeEquiv.symm z))) = _
      rw [AlgEquiv.apply_symm_apply])
  exact h.symm.trans ConicFramePairDegree.pair_field_finrank

local instance image_finite : Module.Finite imageField PairField := by
  apply Module.finite_of_finrank_pos
  rw [image_finrank]
  norm_num

theorem fixed_finrank : Module.finrank fixedField PairField = 576 :=
  ConicFrameIndependentPairAction.finrank_fixedPair

/-- The actual product conic map has exactly the full independent right
tetrahedral fixed field as its image. -/
theorem image_eq_fixed : imageField = fixedField :=
  IntermediateField.eq_of_le_of_finrank_eq' image_le_fixed
    (image_finrank.trans fixed_finrank.symm)

def embeddingIntoFixed : grassmannianPairField →ₐ[ℂ] fixedField where
  toFun z := ⟨functionFieldEmbedding z, fun g => embedding_fixed g z⟩
  map_one' := Subtype.ext functionFieldEmbedding.map_one
  map_zero' := Subtype.ext functionFieldEmbedding.map_zero
  map_add' x y := Subtype.ext (functionFieldEmbedding.map_add x y)
  map_mul' x y := Subtype.ext (functionFieldEmbedding.map_mul x y)
  commutes' c := Subtype.ext (functionFieldEmbedding.commutes c)

/-- The actual native product Grassmannian field, with its original
complex structure map, equals the actual independent right-Γ×Γ quotient. -/
def nativeGrassmannianPairFixedFieldEquiv : grassmannianPairField ≃ₐ[ℂ] fixedField :=
  AlgEquiv.ofBijective embeddingIntoFixed ⟨embeddingIntoFixed.injective, by
    intro x
    have hx : (x : PairField) ∈ imageField := by
      rw [image_eq_fixed]
      exact x.property
    obtain ⟨z,hz⟩ := hx
    exact ⟨z,Subtype.ext hz⟩⟩

@[simp] theorem nativeGrassmannianPairFixedFieldEquiv_coe (z : grassmannianPairField) :
    (nativeGrassmannianPairFixedFieldEquiv z : PairField) = functionFieldEmbedding z := rfl

end M9Native.ConicFramePairFixedField

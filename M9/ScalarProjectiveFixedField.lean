module

public import M9.ConstantFrameElimination
public import M9.ProjectiveNoName

/-!
# Constant scalar invariants are the actual projective ratio field

An explicit normalization splits the homogeneous rational field into its ratio
coefficient field and one radial coordinate. The checked one-dimensional
constant-frame elimination then removes the radial variable. Every action is
the actual substitution by a nonzero constant of the original base field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace M9.ScalarProjectiveFixedField

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (K : Type*) [Field K] (ι : Type*)

abbrev Affine := ProjectiveNoName.Rational K ι
abbrev Homogeneous := ProjectiveNoName.HomogeneousRational K ι
abbrev Radial := ProjectiveNoName.Rational (Affine K ι) Unit
abbrev Normal := ConstantFrameElimination.FunctionField (Affine K ι) 1

def homogeneousVariable (i : ι ⊕ Unit) : Homogeneous K ι :=
  algebraMap (MvPolynomial (ι ⊕ Unit) K) (Homogeneous K ι) (X i)

/-- The literal constant scalar substitution on every homogeneous coordinate. -/
def scalarScale (a : Kˣ) : Homogeneous K ι ≃ₐ[K] Homogeneous K ι :=
  ProjectiveNoName.fractionScale (ι ⊕ Unit) (a : K) a.ne_zero

@[simp] theorem scalarScale_variable (a : Kˣ) (i : ι ⊕ Unit) :
    scalarScale K ι a (homogeneousVariable K ι i) =
      algebraMap K (Homogeneous K ι) (a : K) * homogeneousVariable K ι i :=
  ProjectiveNoName.fractionScale_variable (ι ⊕ Unit) (a : K) a.ne_zero i

theorem scalarScale_one (f : Homogeneous K ι) : scalarScale K ι 1 f = f := by
  have h : (scalarScale K ι 1).toRingHom = RingHom.id (Homogeneous K ι) := by
    apply ProjectiveNoName.rationalRingHom_ext K (ι ⊕ Unit)
    · intro c
      exact (scalarScale K ι 1).commutes c
    · intro i
      change scalarScale K ι 1 (homogeneousVariable K ι i) = homogeneousVariable K ι i
      simp
  exact RingHom.congr_fun h f

theorem scalarScale_mul (a b : Kˣ) (f : Homogeneous K ι) :
    scalarScale K ι (a * b) f = scalarScale K ι a (scalarScale K ι b f) := by
  have h : (scalarScale K ι (a * b)).toRingHom =
      (scalarScale K ι a).toRingHom.comp (scalarScale K ι b).toRingHom := by
    apply ProjectiveNoName.rationalRingHom_ext K (ι ⊕ Unit)
    · intro c
      change scalarScale K ι (a * b) (algebraMap K (Homogeneous K ι) c) =
        scalarScale K ι a (scalarScale K ι b (algebraMap K (Homogeneous K ι) c))
      rw [(scalarScale K ι (a * b)).commutes, (scalarScale K ι b).commutes,
        (scalarScale K ι a).commutes]
    · intro i
      change scalarScale K ι (a * b) (homogeneousVariable K ι i) =
        scalarScale K ι a (scalarScale K ι b (homogeneousVariable K ι i))
      rw [scalarScale_variable, scalarScale_variable, map_mul,
        (scalarScale K ι a).commutes, scalarScale_variable]
      simp only [Units.val_mul, map_mul, mul_assoc]
      ring
  exact RingHom.congr_fun h f

def scalarActionHom : Kˣ →* (Homogeneous K ι ≃ₐ[K] Homogeneous K ι) where
  toFun := scalarScale K ι
  map_one' := AlgEquiv.ext (scalarScale_one K ι)
  map_mul' a b := AlgEquiv.ext (scalarScale_mul K ι a b)

/-- The native fixed intermediate field of all actual constant scalar substitutions. -/
def scalarFixedField : IntermediateField K (Homogeneous K ι) :=
  IntermediateField.fixedField (scalarActionHom K ι).range

theorem mem_scalarFixedField_iff (f : Homogeneous K ι) :
    f ∈ scalarFixedField K ι ↔ ∀ a : Kˣ, scalarScale K ι a f = f := by
  rw [scalarFixedField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h a
    exact h (scalarActionHom K ι a) ⟨a, rfl⟩
  · intro h σ hσ
    obtain ⟨a, rfl⟩ := hσ
    exact h a

/-- Every actual homogeneous ratio is fixed by the original scalar action. -/
theorem scalarScale_ratioEmbedding (a : Kˣ) (f : Affine K ι) :
    scalarScale K ι a (ProjectiveNoName.ratioEmbedding K ι f) =
      ProjectiveNoName.ratioEmbedding K ι f := by
  have h : (scalarScale K ι a).toRingHom.comp
        (ProjectiveNoName.ratioEmbedding K ι).toRingHom =
      (ProjectiveNoName.ratioEmbedding K ι).toRingHom := by
    apply ProjectiveNoName.rationalRingHom_ext K ι
    · intro c
      change scalarScale K ι a
          (ProjectiveNoName.ratioEmbedding K ι (algebraMap K (Affine K ι) c)) =
        ProjectiveNoName.ratioEmbedding K ι (algebraMap K (Affine K ι) c)
      rw [(ProjectiveNoName.ratioEmbedding K ι).commutes, (scalarScale K ι a).commutes]
    · intro i
      change scalarScale K ι a
          (ProjectiveNoName.ratioEmbedding K ι
            (algebraMap (MvPolynomial ι K) (Affine K ι) (X i))) =
        ProjectiveNoName.ratioEmbedding K ι
          (algebraMap (MvPolynomial ι K) (Affine K ι) (X i))
      simp only [ProjectiveNoName.ratioEmbedding_variable, map_div₀]
      change scalarScale K ι a (homogeneousVariable K ι (.inl i)) /
          scalarScale K ι a (homogeneousVariable K ι (.inr ())) = _
      rw [scalarScale_variable, scalarScale_variable]
      exact mul_div_mul_left _ _ (by
        simpa only [map_zero] using (algebraMap K (Homogeneous K ι)).injective.ne a.ne_zero)
  exact RingHom.congr_fun h f

/-- Ratio coefficients and the radial coordinate together give the original field. -/
def radialToHomogeneous : Radial K ι ≃ₐ[K] Homogeneous K ι :=
  (ProjectiveNoName.rationalVariableSwap K ι Unit).trans
    (((ProjectiveNoName.fractionScale ι (ProjectiveNoName.pivot K)⁻¹
      (inv_ne_zero (ProjectiveNoName.pivot_ne_zero K))).restrictScalars K).trans
        (ProjectiveNoName.flatten K ι))

theorem radialToHomogeneous_coefficient (a : Affine K ι) :
    radialToHomogeneous K ι (algebraMap (Affine K ι) (Radial K ι) a) =
      ProjectiveNoName.ratioEmbedding K ι a := by
  have h : (radialToHomogeneous K ι).toRingHom.comp
        (algebraMap (Affine K ι) (Radial K ι)) =
      (ProjectiveNoName.ratioEmbedding K ι).toRingHom := by
    apply ProjectiveNoName.rationalRingHom_ext K ι
    · intro c
      change radialToHomogeneous K ι
          (algebraMap K (Radial K ι) c) =
        ProjectiveNoName.ratioEmbedding K ι (algebraMap K (Affine K ι) c)
      rw [(radialToHomogeneous K ι).commutes, (ProjectiveNoName.ratioEmbedding K ι).commutes]
    · intro i
      change radialToHomogeneous K ι
          (algebraMap (Affine K ι) (Radial K ι)
            (algebraMap (MvPolynomial ι K) (Affine K ι) (X i))) =
        ProjectiveNoName.ratioEmbedding K ι
          (algebraMap (MvPolynomial ι K) (Affine K ι) (X i))
      rw [ProjectiveNoName.ratioEmbedding_variable]
      simp only [radialToHomogeneous, AlgEquiv.trans_apply,
        ProjectiveNoName.rationalVariableSwap_coefficient, AlgEquiv.restrictScalars_apply,
        ProjectiveNoName.fractionScale_variable, map_mul, map_inv₀,
        ProjectiveNoName.flatten_variable, ProjectiveNoName.flatten_pivot]
      rw [div_eq_mul_inv, mul_comm]
  exact RingHom.congr_fun h a

@[simp] theorem radialToHomogeneous_variable :
    radialToHomogeneous K ι
        (algebraMap (MvPolynomial Unit (Affine K ι)) (Radial K ι) (X ())) =
      homogeneousVariable K ι (.inr ()) := by
  simp only [radialToHomogeneous, AlgEquiv.trans_apply,
    ProjectiveNoName.rationalVariableSwap_outer, AlgEquiv.restrictScalars_apply]
  rw [AlgEquiv.commutes]
  change ProjectiveNoName.flatten K ι
    (algebraMap (ProjectiveNoName.PivotField K) (ProjectiveNoName.IteratedField K ι)
      (ProjectiveNoName.pivot K)) = _
  exact ProjectiveNoName.flatten_pivot K ι

def oneIndexEquiv : ConstantFrameElimination.Index 1 ≃ Unit where
  toFun _ := ()
  invFun _ := (0, 0)
  left_inv ij := by rcases ij with ⟨i, j⟩; fin_cases i; fin_cases j; rfl
  right_inv x := by cases x; rfl

/-- The normalization in the exact one-by-one matrix field used by frame elimination. -/
def normalization : Normal K ι ≃ₐ[K] Homogeneous K ι :=
  ((M9.rationalFieldReindex (Affine K ι) oneIndexEquiv).restrictScalars K).trans
    (radialToHomogeneous K ι)

theorem normalization_coefficient (a : Affine K ι) :
    normalization K ι (algebraMap (Affine K ι) (Normal K ι) a) =
      ProjectiveNoName.ratioEmbedding K ι a := by
  change radialToHomogeneous K ι
    (M9.rationalFieldReindex (Affine K ι) oneIndexEquiv
      (algebraMap (Affine K ι) (Normal K ι) a)) = _
  rw [AlgEquiv.commutes, radialToHomogeneous_coefficient]

@[simp] theorem normalization_variable (ij : ConstantFrameElimination.Index 1) :
    normalization K ι
        (algebraMap (ConstantFrameElimination.PolynomialRing (Affine K ι) 1)
          (Normal K ι) (X ij)) =
      homogeneousVariable K ι (.inr ()) := by
  change radialToHomogeneous K ι
    (M9.rationalFieldReindex (Affine K ι) oneIndexEquiv
      (algebraMap (ConstantFrameElimination.PolynomialRing (Affine K ι) 1)
        (Normal K ι) (X ij))) = _
  rw [M9.rationalFieldReindex_algebraMap]
  simp only [MvPolynomial.rename_X]
  exact radialToHomogeneous_variable K ι

def glScalarUnit (g : ConstantFrameElimination.GLn K 1) : Kˣ :=
  Units.mk0 (g.val 0 0) (by
    have h := Matrix.GeneralLinearGroup.det_ne_zero g
    rwa [Matrix.det_fin_one] at h)

variable [Infinite K]

/-- Normalization intertwines every original constant one-by-one frame change
with the literal scalar action on all original homogeneous variables. -/
theorem normalization_leftFraction (g : ConstantFrameElimination.GLn K 1)
    (f : Normal K ι) :
    normalization K ι (ConstantFrameElimination.leftFractionEquiv K (Affine K ι) 1 g f) =
      scalarScale K ι (glScalarUnit K g) (normalization K ι f) := by
  have h : (normalization K ι).toRingHom.comp
        (ConstantFrameElimination.leftFractionEquiv K (Affine K ι) 1 g).toRingHom =
      (scalarScale K ι (glScalarUnit K g)).toRingHom.comp (normalization K ι).toRingHom := by
    apply ProjectiveNoName.rationalRingHom_ext (Affine K ι) (ConstantFrameElimination.Index 1)
    · intro a
      change normalization K ι
          (ConstantFrameElimination.leftFractionEquiv K (Affine K ι) 1 g
            (algebraMap (Affine K ι) (Normal K ι) a)) =
        scalarScale K ι (glScalarUnit K g)
          (normalization K ι (algebraMap (Affine K ι) (Normal K ι) a))
      rw [AlgEquiv.commutes, normalization_coefficient, scalarScale_ratioEmbedding]
    · rintro ⟨i, j⟩
      fin_cases i
      fin_cases j
      change normalization K ι
          (ConstantFrameElimination.leftFractionEquiv K (Affine K ι) 1 g
            (algebraMap (ConstantFrameElimination.PolynomialRing (Affine K ι) 1)
              (Normal K ι) (X (0, 0)))) =
        scalarScale K ι (glScalarUnit K g)
          (normalization K ι
            (algebraMap (ConstantFrameElimination.PolynomialRing (Affine K ι) 1)
              (Normal K ι) (X (0, 0))))
      rw [ConstantFrameElimination.leftFractionEquiv_polynomial]
      simp only [ConstantFrameElimination.leftSubstitution, aeval_X,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue, add_zero, map_mul]
      change normalization K ι
          (algebraMap (Affine K ι) (Normal K ι) (algebraMap K (Affine K ι) (g.val 0 0))) *
          normalization K ι
            (algebraMap (ConstantFrameElimination.PolynomialRing (Affine K ι) 1)
              (Normal K ι) (X (0, 0))) = _
      rw [normalization_coefficient, AlgHom.commutes, normalization_variable,
        scalarScale_variable]
      rfl
  exact RingHom.congr_fun h f

/-- Scalar invariance eliminates the actual radial coordinate. -/
theorem scalarInvariant_iff_ratio (f : Homogeneous K ι) :
    (∀ a : Kˣ, scalarScale K ι a f = f) ↔
      ∃ r : Affine K ι, ProjectiveNoName.ratioEmbedding K ι r = f := by
  constructor
  · intro hf
    let n := (normalization K ι).symm f
    have hn : ∀ g : ConstantFrameElimination.GLn K 1,
        ConstantFrameElimination.leftFractionEquiv K (Affine K ι) 1 g n = n := by
      intro g
      apply (normalization K ι).injective
      rw [normalization_leftFraction]
      change scalarScale K ι (glScalarUnit K g) (normalization K ι ((normalization K ι).symm f)) =
        normalization K ι ((normalization K ι).symm f)
      rw [AlgEquiv.apply_symm_apply, hf]
    obtain ⟨r, hr⟩ := ConstantFrameElimination.invariant_fraction_is_constant
      K (Affine K ι) 1 n hn
    refine ⟨r, ?_⟩
    have h := congrArg (normalization K ι) hr
    rw [normalization_coefficient] at h
    exact h.trans ((normalization K ι).apply_symm_apply f)
  · rintro ⟨r, rfl⟩ a
    exact scalarScale_ratioEmbedding K ι a r

theorem scalarFixedField_eq_ratioField :
    scalarFixedField K ι = ProjectiveNoName.ratioField K ι := by
  ext f
  rw [mem_scalarFixedField_iff, scalarInvariant_iff_ratio]
  exact (AlgHom.mem_fieldRange).symm

/-- The actual ratio embedding, now with codomain the actual scalar fixed field. -/
def ratioFixedEquiv : Affine K ι ≃ₐ[K] scalarFixedField K ι :=
  (ProjectiveNoName.ratioFieldEquiv K ι).trans
    (IntermediateField.equivOfEq (scalarFixedField_eq_ratioField K ι).symm)

@[simp] theorem ratioFixedEquiv_val (r : Affine K ι) :
    (ratioFixedEquiv K ι r).val = ProjectiveNoName.ratioEmbedding K ι r := rfl

/-- Native projective matrix functions are the scalar invariants through the
checked last-coordinate chart of actual projective space. -/
def nativeMatrixFixedEquiv : ProjectiveFunctionField.matrixFunctionField ≃ₐ[ℂ]
    scalarFixedField ℂ (Fin 8) :=
  ProjectiveFunctionField.matrixFunctionFieldEquiv.trans (ratioFixedEquiv ℂ (Fin 8))

theorem nativeMatrixFixedEquiv_val (f : ProjectiveFunctionField.matrixFunctionField) :
    (nativeMatrixFixedEquiv f).val = ProjectiveNoName.ratioEmbedding ℂ (Fin 8)
      (ProjectiveFunctionField.matrixFunctionFieldEquiv f) := rfl

@[simp] theorem nativeMatrixFixedEquiv_coordinateRatio (i : Fin 8) :
    (nativeMatrixFixedEquiv (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)).val =
      homogeneousVariable ℂ (Fin 8) (.inl i) /
        homogeneousVariable ℂ (Fin 8) (.inr ()) := by
  rw [nativeMatrixFixedEquiv_val]
  simp only [ProjectiveFunctionField.matrixFunctionFieldEquiv,
    ProjectiveFunctionField.functionFieldEquiv_coordinateRatio]
  exact ProjectiveNoName.ratioEmbedding_variable ℂ (Fin 8) i

end M9.ScalarProjectiveFixedField

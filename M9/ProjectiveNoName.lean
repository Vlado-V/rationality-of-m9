module

public import M9.FiniteNoNameField
public import M9.ProjectiveFunctionField
public import M9.FrameAction
public import M9.FrameProjectiveGeometry
public import M9.FrameProjectiveRatios
public import M9.WreathFrameComparison
public import M9.ScalarExtendedRepresentation
public import M9.RationalExtensionAssembly
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Projective no-name coordinates and the finite-group comparison

Projective coordinates are actual ratios in the fraction field of the
symmetric algebra.  Normalizing one homogeneous coordinate is proved by
an invertible variable scaling in an iterated rational field.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace M9.ProjectiveNoName

open MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (K : Type*) [Field K] (ι : Type*)

abbrev Rational := FractionRing (MvPolynomial ι K)
abbrev HomogeneousRational := FractionRing (MvPolynomial (ι ⊕ Unit) K)
abbrev PivotField := FractionRing (MvPolynomial Unit K)
abbrev IteratedField := FractionRing (MvPolynomial ι (PivotField K))

theorem rationalRingHom_ext {A : Type*} [Field A] (f g : Rational K ι →+* A)
    (hC : ∀ a : K, f (algebraMap K (Rational K ι) a) = g (algebraMap K (Rational K ι) a))
    (hX : ∀ i : ι, f (algebraMap (MvPolynomial ι K) (Rational K ι) (X i)) =
      g (algebraMap (MvPolynomial ι K) (Rational K ι) (X i))) : f = g := by
  apply IsFractionRing.ringHom_ext (A := MvPolynomial ι K)
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, hX]

/-- A coefficient-field inclusion extends to the actual rational fields. -/
def coefficientPolynomialMap (A : Type*) [Field A] [Algebra K A] :
    MvPolynomial ι K →+* FractionRing (MvPolynomial ι A) :=
  (algebraMap (MvPolynomial ι A) (FractionRing (MvPolynomial ι A))).comp
    (MvPolynomial.map (algebraMap K A))

theorem coefficientPolynomialMap_injective (A : Type*) [Field A] [Algebra K A] :
    Function.Injective (coefficientPolynomialMap K ι A) :=
  (IsFractionRing.injective (MvPolynomial ι A) (FractionRing (MvPolynomial ι A))).comp
    (MvPolynomial.map_injective _ (algebraMap K A).injective)

def coefficientExtend (A : Type*) [Field A] [Algebra K A] :
    Rational K ι →ₐ[K] FractionRing (MvPolynomial ι A) where
  __ := IsFractionRing.lift (coefficientPolynomialMap_injective K ι A)
  commutes' a := by
    change IsFractionRing.lift (coefficientPolynomialMap_injective K ι A)
      (algebraMap (MvPolynomial ι K) (Rational K ι) (C a)) = _
    rw [IsFractionRing.lift_algebraMap]
    simp only [coefficientPolynomialMap, RingHom.comp_apply, MvPolynomial.map_C]
    rfl

theorem coefficientExtend_polynomial (A : Type*) [Field A] [Algebra K A]
    (p : MvPolynomial ι K) :
    coefficientExtend K ι A (algebraMap (MvPolynomial ι K) (Rational K ι) p) =
      algebraMap (MvPolynomial ι A) (FractionRing (MvPolynomial ι A))
        (MvPolynomial.map (algebraMap K A) p) :=
  IsFractionRing.lift_algebraMap (coefficientPolynomialMap_injective K ι A) p

@[simp] theorem coefficientExtend_variable (A : Type*) [Field A] [Algebra K A] (i : ι) :
    coefficientExtend K ι A (algebraMap (MvPolynomial ι K) (Rational K ι) (X i)) =
      algebraMap (MvPolynomial ι A) (FractionRing (MvPolynomial ι A)) (X i) := by
  rw [coefficientExtend_polynomial, MvPolynomial.map_X]

def scaleHom {A : Type*} [Field A] (a : A) : MvPolynomial ι A →ₐ[A] MvPolynomial ι A :=
  aeval fun i => C a * X i

theorem scaleHom_comp {A : Type*} [Field A] (a b : A) :
    (scaleHom ι a).comp (scaleHom ι b) = scaleHom ι (a * b) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, scaleHom, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq]
  ring

theorem scaleHom_one {A : Type*} [Field A] :
    scaleHom ι (1 : A) = AlgHom.id A (MvPolynomial ι A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [scaleHom]

/-- Scaling every affine variable by a nonzero coefficient is an actual
polynomial automorphism over the pivot coefficient field. -/
def scaleVariables {A : Type*} [Field A] (a : A) (ha : a ≠ 0) :
    MvPolynomial ι A ≃ₐ[A] MvPolynomial ι A :=
  AlgEquiv.ofAlgHom (scaleHom ι a) (scaleHom ι a⁻¹)
    (by rw [scaleHom_comp, mul_inv_cancel₀ ha, scaleHom_one])
    (by rw [scaleHom_comp, inv_mul_cancel₀ ha, scaleHom_one])

def fractionScale {A : Type*} [Field A] (a : A) (ha : a ≠ 0) :
    FractionRing (MvPolynomial ι A) ≃ₐ[A] FractionRing (MvPolynomial ι A) :=
  IsFractionRing.algEquivOfAlgEquiv (scaleVariables ι a ha)

@[simp] theorem fractionScale_variable {A : Type*} [Field A] (a : A) (ha : a ≠ 0) (i : ι) :
    fractionScale ι a ha (algebraMap (MvPolynomial ι A) (FractionRing (MvPolynomial ι A)) (X i)) =
      algebraMap A (FractionRing (MvPolynomial ι A)) a *
        algebraMap (MvPolynomial ι A) (FractionRing (MvPolynomial ι A)) (X i) := by
  rw [fractionScale, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change algebraMap (MvPolynomial ι A) (FractionRing (MvPolynomial ι A))
    (scaleHom ι a (X i)) = _
  simp [scaleHom, map_mul]
  rfl

def pivot : PivotField K := algebraMap (MvPolynomial Unit K) (PivotField K) (X ())

theorem pivot_ne_zero : pivot K ≠ 0 := by
  intro h
  exact MvPolynomial.X_ne_zero () ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))

def flatten : IteratedField K ι ≃ₐ[K] HomogeneousRational K ι :=
  M9.rationalFieldSumVariables K Unit ι

@[simp] theorem flatten_variable (i : ι) :
    flatten K ι (algebraMap (MvPolynomial ι (PivotField K)) (IteratedField K ι) (X i)) =
      algebraMap (MvPolynomial (ι ⊕ Unit) K) (HomogeneousRational K ι) (X (Sum.inl i)) := by
  have h := M9.rationalFieldSumVariables_algebraMap K Unit ι
    (X i : MvPolynomial ι (MvPolynomial Unit K))
  have he : algebraMap (MvPolynomial ι (MvPolynomial Unit K)) (IteratedField K ι) (X i) =
      algebraMap (MvPolynomial ι (PivotField K)) (IteratedField K ι) (X i) := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial ι (MvPolynomial Unit K))
      (MvPolynomial ι (PivotField K)) (IteratedField K ι), MvPolynomial.algebraMap_def,
      MvPolynomial.map_X]
  rw [he] at h
  simpa only [flatten, MvPolynomial.sumAlgEquiv_symm_X] using h

@[simp] theorem flatten_pivot :
    flatten K ι (algebraMap (PivotField K) (IteratedField K ι) (pivot K)) =
      algebraMap (MvPolynomial (ι ⊕ Unit) K) (HomogeneousRational K ι) (X (Sum.inr ())) := by
  have h := M9.rationalFieldSumVariables_algebraMap K Unit ι
    (C (X ()) : MvPolynomial ι (MvPolynomial Unit K))
  have he : algebraMap (MvPolynomial ι (MvPolynomial Unit K)) (IteratedField K ι) (C (X ())) =
      algebraMap (PivotField K) (IteratedField K ι) (pivot K) := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial ι (MvPolynomial Unit K))
      (MvPolynomial ι (PivotField K)) (IteratedField K ι), MvPolynomial.algebraMap_def,
      MvPolynomial.map_C]
    rfl
  rw [he] at h
  simpa only [flatten, MvPolynomial.sumAlgEquiv_symm_C_X] using h

/-- Independent affine coordinates embed as the actual homogeneous ratios
`X_i/X_pivot`. Injectivity follows from the constructed field homomorphism. -/
def ratioEmbedding : Rational K ι →ₐ[K] HomogeneousRational K ι :=
  (flatten K ι).toAlgHom.comp
    (((fractionScale ι (pivot K)⁻¹ (inv_ne_zero (pivot_ne_zero K))).restrictScalars K).toAlgHom.comp
      (coefficientExtend K ι (PivotField K)))

@[simp] theorem ratioEmbedding_variable (i : ι) :
    ratioEmbedding K ι (algebraMap (MvPolynomial ι K) (Rational K ι) (X i)) =
      algebraMap (MvPolynomial (ι ⊕ Unit) K) (HomogeneousRational K ι) (X (Sum.inl i)) /
        algebraMap (MvPolynomial (ι ⊕ Unit) K) (HomogeneousRational K ι) (X (Sum.inr ())) := by
  simp only [ratioEmbedding, AlgHom.comp_apply, coefficientExtend_variable,
    AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply,
    fractionScale_variable, map_mul, map_inv₀, flatten_variable, flatten_pivot]
  rw [div_eq_mul_inv, mul_comm]

def ratioField : IntermediateField K (HomogeneousRational K ι) := (ratioEmbedding K ι).fieldRange

def ratioFieldEquiv : Rational K ι ≃ₐ[K] ratioField K ι := (ratioEmbedding K ι).equivFieldRange

section RationalProduct

variable {E F : Type*} [Field E] [Field F] [Algebra K E] [Algebra K F]

def rationalCoefficientEquiv (e : E ≃ₐ[K] F) : Rational E ι ≃ₐ[K] Rational F ι :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.mapAlgEquiv ι e)

@[simp] theorem rationalCoefficientEquiv_variable (e : E ≃ₐ[K] F) (i : ι) :
    rationalCoefficientEquiv K ι e (algebraMap (MvPolynomial ι E) (Rational E ι) (X i)) =
      algebraMap (MvPolynomial ι F) (Rational F ι) (X i) := by
  rw [rationalCoefficientEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp

@[simp] theorem rationalCoefficientEquiv_coefficient (e : E ≃ₐ[K] F) (a : E) :
    rationalCoefficientEquiv K ι e (algebraMap E (Rational E ι) a) =
      algebraMap F (Rational F ι) (e a) := by
  change rationalCoefficientEquiv K ι e
    (algebraMap (MvPolynomial ι E) (Rational E ι) (C a)) = _
  rw [rationalCoefficientEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp only [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_C]
  rfl

end RationalProduct

theorem sumVariables_outer (σ τ : Type*) (i : τ) :
    M9.rationalFieldSumVariables K σ τ
        (algebraMap (MvPolynomial τ (Rational K σ)) (Rational (Rational K σ) τ) (X i)) =
      algebraMap (MvPolynomial (τ ⊕ σ) K) (Rational K (τ ⊕ σ)) (X (Sum.inl i)) := by
  have h := M9.rationalFieldSumVariables_algebraMap K σ τ
    (X i : MvPolynomial τ (MvPolynomial σ K))
  have he : algebraMap (MvPolynomial τ (MvPolynomial σ K)) (Rational (Rational K σ) τ) (X i) =
      algebraMap (MvPolynomial τ (Rational K σ)) (Rational (Rational K σ) τ) (X i) := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial τ (MvPolynomial σ K))
      (MvPolynomial τ (Rational K σ)) (Rational (Rational K σ) τ), MvPolynomial.algebraMap_def,
      MvPolynomial.map_X]
  rw [he] at h
  simpa only [MvPolynomial.sumAlgEquiv_symm_X] using h

theorem sumVariables_coefficient (σ τ : Type*) (i : σ) :
    M9.rationalFieldSumVariables K σ τ
        (algebraMap (Rational K σ) (Rational (Rational K σ) τ)
          (algebraMap (MvPolynomial σ K) (Rational K σ) (X i))) =
      algebraMap (MvPolynomial (τ ⊕ σ) K) (Rational K (τ ⊕ σ)) (X (Sum.inr i)) := by
  have h := M9.rationalFieldSumVariables_algebraMap K σ τ
    (C (X i) : MvPolynomial τ (MvPolynomial σ K))
  have he : algebraMap (MvPolynomial τ (MvPolynomial σ K)) (Rational (Rational K σ) τ) (C (X i)) =
      algebraMap (Rational K σ) (Rational (Rational K σ) τ)
        (algebraMap (MvPolynomial σ K) (Rational K σ) (X i)) := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial τ (MvPolynomial σ K))
      (MvPolynomial τ (Rational K σ)) (Rational (Rational K σ) τ), MvPolynomial.algebraMap_def,
      MvPolynomial.map_C]
    rfl
  rw [he] at h
  simpa only [MvPolynomial.sumAlgEquiv_symm_C_X] using h

/-- The two affine coordinate projections of one product give the same
actual rational function field, with their variables interchanged. -/
def rationalVariableSwap (σ τ : Type*) :
    Rational (Rational K σ) τ ≃ₐ[K] Rational (Rational K τ) σ :=
  (M9.rationalFieldSumVariables K σ τ).trans
    ((M9.rationalFieldReindex K (Equiv.sumComm τ σ)).trans
      (M9.rationalFieldSumVariables K τ σ).symm)

@[simp] theorem rationalVariableSwap_outer (σ τ : Type*) (i : τ) :
    rationalVariableSwap K σ τ
        (algebraMap (MvPolynomial τ (Rational K σ)) (Rational (Rational K σ) τ) (X i)) =
      algebraMap (Rational K τ) (Rational (Rational K τ) σ)
        (algebraMap (MvPolynomial τ K) (Rational K τ) (X i)) := by
  simp only [rationalVariableSwap, AlgEquiv.trans_apply]
  apply (M9.rationalFieldSumVariables K τ σ).injective
  rw [AlgEquiv.apply_symm_apply, sumVariables_outer, sumVariables_coefficient,
    M9.rationalFieldReindex_algebraMap]
  simp

@[simp] theorem rationalVariableSwap_coefficient (σ τ : Type*) (i : σ) :
    rationalVariableSwap K σ τ
        (algebraMap (Rational K σ) (Rational (Rational K σ) τ)
          (algebraMap (MvPolynomial σ K) (Rational K σ) (X i))) =
      algebraMap (MvPolynomial σ (Rational K τ)) (Rational (Rational K τ) σ) (X i) := by
  simp only [rationalVariableSwap, AlgEquiv.trans_apply]
  apply (M9.rationalFieldSumVariables K τ σ).injective
  rw [AlgEquiv.apply_symm_apply, sumVariables_coefficient, sumVariables_outer,
    M9.rationalFieldReindex_algebraMap]
  simp

section CoordinateModule

variable (V : Type*) [AddCommGroup V] [Module K V]

abbrev CoordinateField := FractionRing (SymmetricAlgebra K V)

/-- The actual linear coordinate function associated to a degree-one vector. -/
def linearCoordinate : V →ₗ[K] CoordinateField K V :=
  (IsScalarTower.toAlgHom K (SymmetricAlgebra K V) (CoordinateField K V)).toLinearMap.comp
    (SymmetricAlgebra.ι K V)

/-- The projective coordinate field is generated by all actual ratios of
degree-one coordinates. Its definition uses no choice of basis or chart. -/
def projectiveField : IntermediateField K (CoordinateField K V) :=
  IntermediateField.adjoin K (Set.range fun vw : V × V =>
    linearCoordinate K V vw.1 / linearCoordinate K V vw.2)

def coordinateRatio (v w : V) : projectiveField K V :=
  ⟨linearCoordinate K V v / linearCoordinate K V w,
    IntermediateField.subset_adjoin K _ ⟨(v, w), rfl⟩⟩

theorem coordinateRatio_div (v w z : V) (hz : linearCoordinate K V z ≠ 0) :
    coordinateRatio K V v w = coordinateRatio K V v z / coordinateRatio K V w z := by
  apply Subtype.ext
  exact (div_div_div_cancel_right₀ hz _ _).symm

theorem coordinateRatio_self (v : V) (hv : linearCoordinate K V v ≠ 0) :
    coordinateRatio K V v v = 1 := Subtype.ext (div_self hv)

theorem coordinateRatio_sum {κ : Type*} (s : Finset κ) (a : κ → K) (v : κ → V) (z : V) :
    coordinateRatio K V (∑ i ∈ s, a i • v i) z =
      ∑ i ∈ s, algebraMap K (projectiveField K V) (a i) * coordinateRatio K V (v i) z := by
  apply Subtype.ext
  change (linearCoordinate K V) (∑ i ∈ s, a i • v i) / (linearCoordinate K V) z =
    (projectiveField K V).subtype (∑ i ∈ s,
      algebraMap K (projectiveField K V) (a i) * coordinateRatio K V (v i) z)
  simp only [map_sum, map_mul, map_smul, Algebra.smul_def, Finset.sum_div, mul_div_assoc]
  rfl

def fullCoordinates (b : Module.Basis (ι ⊕ Unit) K V) :
    CoordinateField K V ≃ₐ[K] HomogeneousRational K ι :=
  FiniteNoNameField.rationalCoordinates K V b

@[simp] theorem fullCoordinates_linear_basis (b : Module.Basis (ι ⊕ Unit) K V) (i : ι ⊕ Unit) :
    fullCoordinates K ι V b (linearCoordinate K V (b i)) =
      algebraMap (MvPolynomial (ι ⊕ Unit) K) (HomogeneousRational K ι) (X i) := by
  change FiniteNoNameField.rationalCoordinates K V b
    (algebraMap (SymmetricAlgebra K V) (CoordinateField K V) (SymmetricAlgebra.ι K V (b i))) = _
  rw [FiniteNoNameField.rationalCoordinates_polynomial]
  simp only [FiniteNoNameField.polynomialCoordinates, SymmetricAlgebra.equivMvPolynomial_ι_apply]

theorem basisPivot_ne_zero (b : Module.Basis (ι ⊕ Unit) K V) :
    linearCoordinate K V (b (Sum.inr ())) ≠ 0 := by
  intro h
  have hh := congrArg (fullCoordinates K ι V b) h
  rw [fullCoordinates_linear_basis, map_zero] at hh
  exact MvPolynomial.X_ne_zero (Sum.inr ())
    ((IsFractionRing.injective _ _) (hh.trans (map_zero _).symm))

def basisRatioEmbedding (b : Module.Basis (ι ⊕ Unit) K V) :
    Rational K ι →ₐ[K] CoordinateField K V :=
  (fullCoordinates K ι V b).symm.toAlgHom.comp (ratioEmbedding K ι)

@[simp] theorem basisRatioEmbedding_variable (b : Module.Basis (ι ⊕ Unit) K V) (i : ι) :
    basisRatioEmbedding K ι V b (algebraMap (MvPolynomial ι K) (Rational K ι) (X i)) =
      linearCoordinate K V (b (Sum.inl i)) / linearCoordinate K V (b (Sum.inr ())) := by
  apply (fullCoordinates K ι V b).injective
  simp only [basisRatioEmbedding, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, ratioEmbedding_variable, map_div₀, fullCoordinates_linear_basis]

def basisRatioField (b : Module.Basis (ι ⊕ Unit) K V) : IntermediateField K (CoordinateField K V) :=
  (basisRatioEmbedding K ι V b).fieldRange

theorem basis_ratio_mem (b : Module.Basis (ι ⊕ Unit) K V) (i : ι ⊕ Unit) :
    linearCoordinate K V (b i) / linearCoordinate K V (b (Sum.inr ())) ∈ basisRatioField K ι V b := by
  cases i with
  | inl i =>
    exact ⟨algebraMap (MvPolynomial ι K) (Rational K ι) (X i), basisRatioEmbedding_variable K ι V b i⟩
  | inr i =>
    cases i
    rw [div_self (basisPivot_ne_zero K ι V b)]
    exact IntermediateField.one_mem _

variable [Fintype ι]

theorem normalized_linear_mem (b : Module.Basis (ι ⊕ Unit) K V) (v : V) :
    linearCoordinate K V v / linearCoordinate K V (b (Sum.inr ())) ∈ basisRatioField K ι V b := by
  rw [← b.sum_repr v, map_sum, Finset.sum_div]
  apply IntermediateField.sum_mem
  intro i _
  rw [map_smul, Algebra.smul_def, mul_div_assoc]
  exact (basisRatioField K ι V b).mul_mem
    ((basisRatioField K ι V b).algebraMap_mem _) (basis_ratio_mem K ι V b i)

theorem linear_ratio_mem (b : Module.Basis (ι ⊕ Unit) K V) (v w : V) :
    linearCoordinate K V v / linearCoordinate K V w ∈ basisRatioField K ι V b := by
  have h := (basisRatioField K ι V b).div_mem
    (normalized_linear_mem K ι V b v) (normalized_linear_mem K ι V b w)
  rwa [div_div_div_cancel_right₀ (basisPivot_ne_zero K ι V b)] at h

theorem projectiveField_le_basisRatioField (b : Module.Basis (ι ⊕ Unit) K V) :
    projectiveField K V ≤ basisRatioField K ι V b := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨⟨v, w⟩, rfl⟩
  exact linear_ratio_mem K ι V b v w

omit [Fintype ι] in
theorem basisRatioField_le_projectiveField (b : Module.Basis (ι ⊕ Unit) K V) :
    basisRatioField K ι V b ≤ projectiveField K V := by
  rintro _ ⟨f, rfl⟩
  have hp : ∀ p : MvPolynomial ι K,
      basisRatioEmbedding K ι V b (algebraMap (MvPolynomial ι K) (Rational K ι) p) ∈
        projectiveField K V := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      change basisRatioEmbedding K ι V b (algebraMap K (Rational K ι) a) ∈ _
      rw [(basisRatioEmbedding K ι V b).commutes]
      exact IntermediateField.algebraMap_mem _ _
    | add p q hp hq =>
      rw [map_add, map_add]
      exact (projectiveField K V).add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul, basisRatioEmbedding_variable]
      apply (projectiveField K V).mul_mem hp
      exact IntermediateField.subset_adjoin K _ ⟨(b (Sum.inl i), b (Sum.inr ())), rfl⟩
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial ι K) f
  rw [map_div₀]
  exact (projectiveField K V).div_mem (hp p) (hp q)

/-- Actual projective coordinates are independent of the chosen basis. -/
theorem projectiveField_eq_basisRatioField (b : Module.Basis (ι ⊕ Unit) K V) :
    projectiveField K V = basisRatioField K ι V b :=
  le_antisymm (projectiveField_le_basisRatioField K ι V b) (basisRatioField_le_projectiveField K ι V b)

/-- Normalizing one homogeneous coordinate gives an actual rational-field
isomorphism, with precisely the expected ratio variables. -/
def projectiveFieldEquiv (b : Module.Basis (ι ⊕ Unit) K V) :
    Rational K ι ≃ₐ[K] projectiveField K V :=
  (basisRatioEmbedding K ι V b).equivFieldRange.trans
    (IntermediateField.equivOfEq (projectiveField_eq_basisRatioField K ι V b).symm)

@[simp] theorem projectiveFieldEquiv_apply_coe (b : Module.Basis (ι ⊕ Unit) K V) (f : Rational K ι) :
    (projectiveFieldEquiv K ι V b f : CoordinateField K V) = basisRatioEmbedding K ι V b f := rfl

@[simp] theorem projectiveFieldEquiv_variable (b : Module.Basis (ι ⊕ Unit) K V) (i : ι) :
    projectiveFieldEquiv K ι V b (algebraMap (MvPolynomial ι K) (Rational K ι) (X i)) =
      coordinateRatio K V (b (Sum.inl i)) (b (Sum.inr ())) :=
  Subtype.ext (basisRatioEmbedding_variable K ι V b i)

section Semilinear

variable (G : Type*) [Group G] [MulSemiringAction G K]
  [DistribMulAction G V] [SMulDistribClass G K V]

theorem projectiveField_smul_mem (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) (g : G)
    (x : CoordinateField K V) (hx : x ∈ projectiveField K V) :
    letI := FiniteNoNameField.symmetricRationalAction G K V b
    g • x ∈ projectiveField K V := by
  let := FiniteNoNameField.symmetricRationalAction G K V b
  change g • x ∈ projectiveField K V
  refine IntermediateField.adjoin_induction (F := K)
    (motive := fun y _ => g • y ∈ projectiveField K V) ?_ ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨v, w⟩, rfl⟩
    change g • (algebraMap (SymmetricAlgebra K V) (CoordinateField K V) (SymmetricAlgebra.ι K V v) /
      algebraMap (SymmetricAlgebra K V) (CoordinateField K V) (SymmetricAlgebra.ι K V w)) ∈ _
    rw [smul_div₀', FiniteNoNameField.symmetricRationalAction_iota G K V b hb,
      FiniteNoNameField.symmetricRationalAction_iota G K V b hb]
    exact IntermediateField.subset_adjoin K _ ⟨(g • v, g • w), rfl⟩
  · intro a
    rw [FiniteNoNameField.symmetricRationalAction_constant]
    exact IntermediateField.algebraMap_mem _ _
  · intro y z _ _ hy hz
    rw [smul_add]
    exact (projectiveField K V).add_mem hy hz
  · intro y _ hy
    rw [smul_inv'']
    exact (projectiveField K V).inv_mem hy
  · intro y z _ _ hy hz
    rw [smul_mul']
    exact (projectiveField K V).mul_mem hy hz

def projectiveRepresentation (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) :
    G →* (projectiveField K V ≃+* projectiveField K V) := by
  let := FiniteNoNameField.symmetricRationalAction G K V b
  exact
  { toFun := fun g =>
      { toFun := fun x => ⟨g • x.val, projectiveField_smul_mem K ι V G b hb g x.val x.property⟩
        invFun := fun x => ⟨g⁻¹ • x.val, projectiveField_smul_mem K ι V G b hb g⁻¹ x.val x.property⟩
        left_inv := fun x => Subtype.ext (inv_smul_smul g x.val)
        right_inv := fun x => Subtype.ext (smul_inv_smul g x.val)
        map_mul' := fun x y => Subtype.ext (smul_mul' g x.val y.val)
        map_add' := fun x y => Subtype.ext (smul_add g x.val y.val) }
    map_one' := by ext x; exact one_smul G x.val
    map_mul' := fun g h => by ext x; exact mul_smul g h x.val }

@[instance_reducible] def projectiveAction (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) : MulSemiringAction G (projectiveField K V) :=
  MulSemiringAction.compHom _ (projectiveRepresentation K ι V G b hb)

/-- The constructed projective action has the actual expected value on
every ratio of degree-one coordinates. -/
theorem projectiveAction_coordinateRatio (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) (g : G) (v w : V) :
    letI := projectiveAction K ι V G b hb
    g • coordinateRatio K V v w = coordinateRatio K V (g • v) (g • w) := by
  let := FiniteNoNameField.symmetricRationalAction G K V b
  apply Subtype.ext
  change g • (algebraMap (SymmetricAlgebra K V) (CoordinateField K V) (SymmetricAlgebra.ι K V v) /
      algebraMap (SymmetricAlgebra K V) (CoordinateField K V) (SymmetricAlgebra.ι K V w)) = _
  rw [smul_div₀', FiniteNoNameField.symmetricRationalAction_iota G K V b hb,
    FiniteNoNameField.symmetricRationalAction_iota G K V b hb]
  rfl

/-- In a fixed basis, the genuine ratio coordinates intertwine the action
with the coefficientwise action on independent affine rational variables. -/
theorem basisRatioEmbedding_smul (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) (g : G) (f : Rational K ι) :
    letI := FiniteNoNameField.symmetricRationalAction G K V b
    basisRatioEmbedding K ι V b (g • f) = g • basisRatioEmbedding K ι V b f := by
  let := FiniteNoNameField.symmetricRationalAction G K V b
  let J := (basisRatioEmbedding K ι V b).toRingHom.comp
    (algebraMap (MvPolynomial ι K) (Rational K ι))
  have hp : ∀ p : MvPolynomial ι K, J (g • p) = g • J p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [FiniteNoNameField.polynomialAction_apply, MvPolynomial.map_C]
      change basisRatioEmbedding K ι V b (algebraMap K (Rational K ι) (g • a)) =
        g • basisRatioEmbedding K ι V b (algebraMap K (Rational K ι) a)
      rw [(basisRatioEmbedding K ι V b).commutes, (basisRatioEmbedding K ι V b).commutes]
      exact (FiniteNoNameField.symmetricRationalAction_constant G K V b g a).symm
    | add p q hp hq => rw [smul_add, map_add, map_add, smul_add, hp, hq]
    | mul_X p i hp =>
      rw [smul_mul', map_mul, map_mul, smul_mul', hp]
      congr 1
      change basisRatioEmbedding K ι V b
          (algebraMap (MvPolynomial ι K) (Rational K ι) (g • X i)) =
        g • basisRatioEmbedding K ι V b (algebraMap (MvPolynomial ι K) (Rational K ι) (X i))
      rw [FiniteNoNameField.polynomialAction_apply, MvPolynomial.map_X, basisRatioEmbedding_variable]
      change _ = g • (algebraMap (SymmetricAlgebra K V) (CoordinateField K V)
        (SymmetricAlgebra.ι K V (b (Sum.inl i))) /
          algebraMap (SymmetricAlgebra K V) (CoordinateField K V)
            (SymmetricAlgebra.ι K V (b (Sum.inr ()))))
      rw [smul_div₀', FiniteNoNameField.symmetricRationalAction_iota G K V b hb,
        FiniteNoNameField.symmetricRationalAction_iota G K V b hb, hb, hb]
      rfl
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial ι K) f
  rw [smul_div₀', map_div₀, map_div₀, smul_div₀', FiniteNoNameField.rationalAction_polynomial,
    FiniteNoNameField.rationalAction_polynomial]
  exact congrArg₂ (fun x y : CoordinateField K V => x / y) (hp p) (hp q)

theorem projectiveFieldEquiv_smul (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) (g : G) (f : Rational K ι) :
    letI := projectiveAction K ι V G b hb
    projectiveFieldEquiv K ι V b (g • f) = g • projectiveFieldEquiv K ι V b f := by
  apply Subtype.ext
  change basisRatioEmbedding K ι V b (g • f) =
    (letI := FiniteNoNameField.symmetricRationalAction G K V b;
      g • basisRatioEmbedding K ι V b f)
  exact basisRatioEmbedding_smul K ι V G b hb g f

def projectiveFixedField (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) : Subfield (projectiveField K V) :=
  letI := projectiveAction K ι V G b hb
  FixedPoints.subfield G (projectiveField K V)

def projectiveFixedBaseEmbedding (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) :
    FixedPoints.subfield G K →+* projectiveFixedField K ι V G b hb where
  toFun a := ⟨algebraMap K (projectiveField K V) (a : K), by
    intro g
    apply Subtype.ext
    change (letI := FiniteNoNameField.symmetricRationalAction G K V b;
      g • algebraMap K (CoordinateField K V) (a : K)) = algebraMap K (CoordinateField K V) (a : K)
    rw [FiniteNoNameField.symmetricRationalAction_constant, a.property g]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

instance projectiveFixedAlgebra (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) :
    Algebra (FixedPoints.subfield G K) (projectiveFixedField K ι V G b hb) :=
  (projectiveFixedBaseEmbedding K ι V G b hb).toAlgebra

def fixedProjectiveCoordinates (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) :
    FiniteNoNameField.FixedRationalField G K ι ≃ₐ[FixedPoints.subfield G K]
      projectiveFixedField K ι V G b hb := by
  letI := projectiveAction K ι V G b hb
  let e := projectiveFieldEquiv K ι V b
  exact
  { toFun := fun a => ⟨e a.val, fun g => by
      rw [← projectiveFieldEquiv_smul K ι V G b hb g a.val, a.property g]⟩
    invFun := fun x => ⟨e.symm x.val, fun g => by
      apply e.injective
      rw [projectiveFieldEquiv_smul K ι V G b hb, e.apply_symm_apply, x.property g]⟩
    left_inv := fun a => Subtype.ext (e.symm_apply_apply a.val)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
    map_add' := fun a b => Subtype.ext (map_add e a.val b.val)
    map_mul' := fun a b => Subtype.ext (map_mul e a.val b.val)
    commutes' := fun a => by
      apply Subtype.ext
      exact e.commutes (a : K) }

/-- Projectivized finite no-name: one fixed homogeneous coordinate is
normalized, leaving `card ι` genuinely independent invariant variables. -/
def projectiveFixedFieldAlgEquiv [Finite G] (b : Module.Basis (ι ⊕ Unit) K V)
    (hb : ∀ (g : G) (i : ι ⊕ Unit), g • b i = b i) :
    Rational (FixedPoints.subfield G K) ι ≃ₐ[FixedPoints.subfield G K]
      projectiveFixedField K ι V G b hb :=
  (FiniteNoNameField.fixedRationalAlgEquiv G K ι).trans (fixedProjectiveCoordinates K ι V G b hb)

section AutomaticBasis

variable [Finite G] [FaithfulSMul G K] [FiniteDimensional K V]

/-- The projective fixed basis is constructed from the original action,
then reindexed into affine coordinates and one distinguished pivot. -/
def splitInvariantBasis (n : ℕ) (hdim : Module.finrank K V = n + 1) :
    Module.Basis (Fin n ⊕ Unit) K V :=
  (FiniteGaloisDescent.invariantBasis G K V).reindex
    (Fintype.equivOfCardEq (show Fintype.card (Fin (Module.finrank K V)) =
      Fintype.card (Fin n ⊕ Unit) by simp [hdim]))

theorem splitInvariantBasis_fixed (n : ℕ) (hdim : Module.finrank K V = n + 1)
    (g : G) (i : Fin n ⊕ Unit) : g • splitInvariantBasis K V G n hdim i =
      splitInvariantBasis K V G n hdim i := by
  simp only [splitInvariantBasis, Module.Basis.coe_reindex, Function.comp_apply]
  exact FiniteGaloisDescent.invariantBasis_fixed G K V g _

/-- The actual invariant projective-coordinate field, with its action
constructed from genuine semilinear descent. -/
abbrev ProjectiveNoNameFixedField (n : ℕ) (hdim : Module.finrank K V = n + 1) :=
  projectiveFixedField K (Fin n) V G (splitInvariantBasis K V G n hdim)
    (splitInvariantBasis_fixed K V G n hdim)

/-- The projectivized no-name endpoint has exactly one fewer independent
variable than the original semilinear coordinate module. -/
def projectiveNoNameAlgEquiv (n : ℕ) (hdim : Module.finrank K V = n + 1) :
    M9.RationalField (FixedPoints.subfield G K) n ≃ₐ[FixedPoints.subfield G K]
      ProjectiveNoNameFixedField K V G n hdim :=
  projectiveFixedFieldAlgEquiv K (Fin n) V G (splitInvariantBasis K V G n hdim)
    (splitInvariantBasis_fixed K V G n hdim)

end AutomaticBasis

end Semilinear

end CoordinateModule

section FixedFieldTransport

variable (G : Type*) [Group G]
variable {E F : Type*} [Field E] [Field F] [MulSemiringAction G E] [MulSemiringAction G F]

/-- An equivariant actual field isomorphism restricts to the actual fixed
subfields. This conclusion is derived from equivariance, not supplied as data. -/
def fixedFieldEquivOfEquivariant (e : E ≃+* F)
    (he : ∀ (g : G) (x : E), e (g • x) = g • e x) :
    FixedPoints.subfield G E ≃+* FixedPoints.subfield G F where
  toFun x := ⟨e x.val, fun g => by rw [← he, x.property g]⟩
  invFun y := ⟨e.symm y.val, fun g => by
    apply e.injective
    rw [he, e.apply_symm_apply, y.property g]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_mul' x y := Subtype.ext (map_mul e x.val y.val)

variable (C : Type*) [Field C] [Algebra C E] [Algebra C F]
  [SMulCommClass G C E] [SMulCommClass G C F]

def fixedIntermediateField (E : Type*) [Field E] [Algebra C E]
    [MulSemiringAction G E] [SMulCommClass G C E] : IntermediateField C E where
  __ := FixedPoints.subfield G E
  algebraMap_mem' a g := smul_algebraMap g a

def fixedIntermediateAlgEquiv (e : E ≃ₐ[C] F)
    (he : ∀ (g : G) (x : E), e (g • x) = g • e x) :
    fixedIntermediateField G C E ≃ₐ[C] fixedIntermediateField G C F where
  __ := fixedFieldEquivOfEquivariant G e.toRingEquiv he
  commutes' a := Subtype.ext (e.commutes a)

end FixedFieldTransport

section AffineNoNameCoordinates

variable [Fintype ι] (U G : Type*) [AddCommGroup U] [Module K U]
  [Group G] [MulSemiringAction G K] [DistribMulAction G U] [SMulDistribClass G K U]
  [Finite G] [FaithfulSMul G K] [FiniteDimensional K U]

def affineInvariantBasis (b₀ : Module.Basis ι K U) : Module.Basis ι K U :=
  (FiniteGaloisDescent.invariantBasis G K U).reindex
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b₀]))

theorem affineInvariantBasis_fixed (b₀ : Module.Basis ι K U) (g : G) (i : ι) :
    g • affineInvariantBasis K ι U G b₀ i = affineInvariantBasis K ι U G b₀ i := by
  simp only [affineInvariantBasis, Module.Basis.coe_reindex, Function.comp_apply]
  exact FiniteGaloisDescent.invariantBasis_fixed G K U g _

/-- The action on a polynomial-coordinate fraction field is transported
from the actual semilinear coordinate module through its specified basis. -/
@[instance_reducible] def affineFieldAction (b₀ : Module.Basis ι K U) :
    MulSemiringAction G (Rational K ι) :=
  letI := FiniteNoNameField.symmetricRationalAction G K U (affineInvariantBasis K ι U G b₀)
  FiniteNoNameField.transportAction G (FiniteNoNameField.rationalCoordinates K U b₀).symm.toRingEquiv

theorem affineFieldAction_coefficient (b₀ : Module.Basis ι K U) (g : G) (a : K) :
    letI := affineFieldAction K ι U G b₀
    g • algebraMap K (Rational K ι) a = algebraMap K (Rational K ι) (g • a) := by
  let := FiniteNoNameField.symmetricRationalAction G K U (affineInvariantBasis K ι U G b₀)
  change FiniteNoNameField.rationalCoordinates K U b₀
    (g • (FiniteNoNameField.rationalCoordinates K U b₀).symm
      (algebraMap K (Rational K ι) a)) = _
  rw [(FiniteNoNameField.rationalCoordinates K U b₀).symm.commutes,
    FiniteNoNameField.symmetricRationalAction_constant,
    (FiniteNoNameField.rationalCoordinates K U b₀).commutes]

theorem affineFieldAction_variable (b₀ : Module.Basis ι K U) (g : G) (i : ι) :
    letI := affineFieldAction K ι U G b₀
    g • algebraMap (MvPolynomial ι K) (Rational K ι) (X i) =
      FiniteNoNameField.rationalCoordinates K U b₀
        (algebraMap (SymmetricAlgebra K U) (FiniteNoNameField.CoordinateField K U)
          (SymmetricAlgebra.ι K U (g • b₀ i))) := by
  let := FiniteNoNameField.symmetricRationalAction G K U (affineInvariantBasis K ι U G b₀)
  have hi : (FiniteNoNameField.rationalCoordinates K U b₀).symm
      (algebraMap (MvPolynomial ι K) (Rational K ι) (X i)) =
        algebraMap (SymmetricAlgebra K U) (FiniteNoNameField.CoordinateField K U)
          (SymmetricAlgebra.ι K U (b₀ i)) := by
    apply (FiniteNoNameField.rationalCoordinates K U b₀).injective
    rw [AlgEquiv.apply_symm_apply, FiniteNoNameField.rationalCoordinates_polynomial]
    simp only [FiniteNoNameField.polynomialCoordinates, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  change FiniteNoNameField.rationalCoordinates K U b₀
    (g • (FiniteNoNameField.rationalCoordinates K U b₀).symm
      (algebraMap (MvPolynomial ι K) (Rational K ι) (X i))) = _
  rw [hi, FiniteNoNameField.symmetricRationalAction_iota G K U _
    (affineInvariantBasis_fixed K ι U G b₀)]

theorem affineFieldAction_variable_of_permutation (b₀ : Module.Basis ι K U)
    (π : G →* Equiv.Perm ι) (hπ : ∀ g i, g • b₀ i = b₀ (π g i)) (g : G) (i : ι) :
    letI := affineFieldAction K ι U G b₀
    g • algebraMap (MvPolynomial ι K) (Rational K ι) (X i) =
      algebraMap (MvPolynomial ι K) (Rational K ι) (X (π g i)) := by
  rw [affineFieldAction_variable, hπ, FiniteNoNameField.rationalCoordinates_polynomial]
  simp only [FiniteNoNameField.polynomialCoordinates, SymmetricAlgebra.equivMvPolynomial_ι_apply]

def affineFixedField (b₀ : Module.Basis ι K U) : Subfield (Rational K ι) :=
  letI := affineFieldAction K ι U G b₀
  FixedPoints.subfield G (Rational K ι)

def affineFixedBaseEmbedding (b₀ : Module.Basis ι K U) :
    FixedPoints.subfield G K →+* affineFixedField K ι U G b₀ where
  toFun a := ⟨algebraMap K (Rational K ι) (a : K), fun g => by
    rw [affineFieldAction_coefficient, a.property g]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

instance affineFixedAlgebra (b₀ : Module.Basis ι K U) :
    Algebra (FixedPoints.subfield G K) (affineFixedField K ι U G b₀) :=
  (affineFixedBaseEmbedding K ι U G b₀).toAlgebra

def affineFixedToSymmetricEquiv (b₀ : Module.Basis ι K U) :
    affineFixedField K ι U G b₀ ≃ₐ[FixedPoints.subfield G K]
      FiniteNoNameField.SymmetricFixedField G K U (affineInvariantBasis K ι U G b₀) := by
  let := FiniteNoNameField.symmetricRationalAction G K U (affineInvariantBasis K ι U G b₀)
  exact
  { __ := FiniteNoNameField.transportFixedEquiv G (FiniteNoNameField.rationalCoordinates K U b₀).symm.toRingEquiv
    commutes' := fun a => by
      apply Subtype.ext
      exact (FiniteNoNameField.rationalCoordinates K U b₀).symm.commutes (a : K) }

/-- Affine finite no-name for the actual rational field in a specified
coordinate basis, with the action verified on constants and variables. -/
def affineNoNameAlgEquiv (b₀ : Module.Basis ι K U) :
    affineFixedField K ι U G b₀ ≃ₐ[FixedPoints.subfield G K]
      Rational (FixedPoints.subfield G K) ι :=
  (affineFixedToSymmetricEquiv K ι U G b₀).trans
    (FiniteNoNameField.fixedSymmetricFieldAlgEquiv G K U (affineInvariantBasis K ι U G b₀))

end AffineNoNameCoordinates

namespace Concrete

abbrev W := FrameAction.TetrahedralFrameGroup
abbrev NativeField := ProjectiveFunctionField.matrixFunctionField
abbrev AffineIndex := SymmetricBlockInvariants.BlockIndex
abbrev AffineField := WreathFrameComparison.FramePermutationField ℂ

local instance nativeFieldAction : MulSemiringAction W NativeField := FrameProjectiveGeometry.fieldAction
local instance nativeFieldScalarCommutes : SMulCommClass W ℂ NativeField := FrameProjectiveGeometry.fieldScalarCommutes
local instance nativeFieldFaithful : FaithfulSMul W NativeField := FrameProjectiveGeometry.fieldAction_faithful

/-- The actual rational function field obtained by adjoining the eight
affine coordinates to the native projective generic stalk. -/
abbrev ProductField := Rational NativeField AffineIndex

theorem nativeRingHom_ext {A : Type*} [Field A] (f g : NativeField →+* A)
    (hC : ∀ c : ℂ, f (algebraMap ℂ NativeField c) = g (algebraMap ℂ NativeField c))
    (hP : ∀ i : Fin 8, f (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i) =
      g (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) : f = g := by
  let e := ProjectiveFunctionField.matrixFunctionFieldEquiv
  have hr : f.comp e.symm.toRingHom = g.comp e.symm.toRingHom := by
    apply rationalRingHom_ext ℂ (Fin 8)
    · intro c
      change f (e.symm (algebraMap ℂ (Rational ℂ (Fin 8)) c)) =
        g (e.symm (algebraMap ℂ (Rational ℂ (Fin 8)) c))
      rw [e.symm.commutes]
      exact hC c
    · intro i
      have he : e.symm (algebraMap (MvPolynomial (Fin 8) ℂ) (M9.RationalField ℂ 8) (X i)) =
          ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i := by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply]
        exact (ProjectiveFunctionField.functionFieldEquiv_coordinateRatio 8 (Fin.last 8) i).symm
      change f (e.symm (algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8)) (X i))) =
        g (e.symm (algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8)) (X i)))
      rw [he]
      exact hP i
  apply RingHom.ext
  intro x
  have h := congrArg (fun h : M9.RationalField ℂ 8 →+* A => h (e x)) hr
  change f (e.symm (e x)) = g (e.symm (e x)) at h
  simpa only [e.symm_apply_apply] using h

/-- Ring maps from the genuine product field are determined by the two
groups of eight chart coordinates and the original complex constants. -/
theorem productRingHom_ext {A : Type*} [Field A] (f g : ProductField →+* A)
    (hC : ∀ c : ℂ, f (algebraMap ℂ ProductField c) = g (algebraMap ℂ ProductField c))
    (hU : ∀ i : AffineIndex,
      f (algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i)) =
        g (algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i)))
    (hP : ∀ i : Fin 8,
      f (algebraMap NativeField ProductField (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) =
        g (algebraMap NativeField ProductField (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i))) :
    f = g := by
  have hc : f.comp (algebraMap NativeField ProductField) = g.comp (algebraMap NativeField ProductField) := by
    apply nativeRingHom_ext
    · intro c
      change f (algebraMap NativeField ProductField (algebraMap ℂ NativeField c)) = _
      rw [← IsScalarTower.algebraMap_apply ℂ NativeField ProductField]
      exact hC c
    · exact hP
  apply rationalRingHom_ext NativeField AffineIndex f g
  · intro a
    exact congrArg (fun h : NativeField →+* A => h a) hc
  · exact hU

/-- The two product projections are related by the native projective
chart and a literal interchange of independent rational variables. -/
def productChartEquiv : ProductField ≃ₐ[ℂ] Rational AffineField (Fin 8) :=
  (rationalCoefficientEquiv ℂ AffineIndex ProjectiveFunctionField.matrixFunctionFieldEquiv).trans
    (rationalVariableSwap ℂ (Fin 8) AffineIndex)

@[simp] theorem productChartEquiv_affine (i : AffineIndex) :
    productChartEquiv (algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i)) =
      algebraMap AffineField (Rational AffineField (Fin 8)) (PermutationInvariants.coordinate ℂ i) := by
  simp only [productChartEquiv, AlgEquiv.trans_apply, rationalCoefficientEquiv_variable,
    rationalVariableSwap_outer]
  rfl

@[simp] theorem productChartEquiv_projective (i : Fin 8) :
    productChartEquiv (algebraMap NativeField ProductField
      (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) =
      algebraMap (MvPolynomial (Fin 8) AffineField) (Rational AffineField (Fin 8)) (X i) := by
  rw [productChartEquiv, AlgEquiv.trans_apply, rationalCoefficientEquiv_coefficient]
  simp only [ProjectiveFunctionField.matrixFunctionFieldEquiv,
    ProjectiveFunctionField.functionFieldEquiv_coordinateRatio]
  exact rationalVariableSwap_coefficient ℂ (Fin 8) AffineIndex i

section RelativeChart

variable (V : Type*) [AddCommGroup V] [Module AffineField V]

/-- The product field is the actual projective ratio field of the scalar
extended nine-dimensional coordinate module, in any specified basis. -/
def relativeProductRingEquiv (b : Module.Basis (Fin 8 ⊕ Unit) AffineField V) :
    ProductField ≃+* projectiveField AffineField V :=
  productChartEquiv.toRingEquiv.trans (projectiveFieldEquiv AffineField (Fin 8) V b).toRingEquiv

@[simp] theorem relativeProductRingEquiv_affine
    (b : Module.Basis (Fin 8 ⊕ Unit) AffineField V) (i : AffineIndex) :
    relativeProductRingEquiv V b (algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i)) =
      algebraMap AffineField (projectiveField AffineField V) (PermutationInvariants.coordinate ℂ i) := by
  rw [relativeProductRingEquiv, RingEquiv.trans_apply]
  change projectiveFieldEquiv AffineField (Fin 8) V b (productChartEquiv _) = _
  rw [productChartEquiv_affine, (projectiveFieldEquiv AffineField (Fin 8) V b).commutes]

@[simp] theorem relativeProductRingEquiv_projective
    (b : Module.Basis (Fin 8 ⊕ Unit) AffineField V) (i : Fin 8) :
    relativeProductRingEquiv V b (algebraMap NativeField ProductField
      (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) =
      coordinateRatio AffineField V (b (Sum.inl i)) (b (Sum.inr ())) := by
  rw [relativeProductRingEquiv, RingEquiv.trans_apply]
  change projectiveFieldEquiv AffineField (Fin 8) V b (productChartEquiv _) = _
  rw [productChartEquiv_projective, projectiveFieldEquiv_variable]

end RelativeChart

abbrev AffineCoordinateModule := ScalarExtendedRepresentation.PermutationModule NativeField

def affineCoordinateBasis : Module.Basis AffineIndex NativeField AffineCoordinateModule :=
  ScalarExtendedRepresentation.permutationBasis NativeField

/-- The actual diagonal action on the native projective field with eight
adjoined affine coordinates. -/
@[instance_reducible] def productAction : MulSemiringAction W ProductField :=
  affineFieldAction NativeField AffineIndex AffineCoordinateModule W affineCoordinateBasis

theorem productAction_coefficient (g : W) (a : NativeField) :
    letI := productAction
    g • algebraMap NativeField ProductField a = algebraMap NativeField ProductField (g • a) :=
  affineFieldAction_coefficient NativeField AffineIndex AffineCoordinateModule W affineCoordinateBasis g a

theorem productAction_affine (g : W) (i : AffineIndex) :
    letI := productAction
    g • algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i) =
      algebraMap (MvPolynomial AffineIndex NativeField) ProductField
        (X (WreathFrameComparison.frameIndexRepresentation g i)) :=
  affineFieldAction_variable_of_permutation NativeField AffineIndex AffineCoordinateModule W
    affineCoordinateBasis WreathFrameComparison.frameIndexRepresentation
      (ScalarExtendedRepresentation.permutationBasis_action NativeField) g i

/-- The coefficient invariant field is the actual native projective invariant field. -/
def nativeFixedField : IntermediateField ℂ NativeField := fixedIntermediateField W ℂ NativeField

abbrev productFixedField : Subfield ProductField :=
  affineFixedField NativeField AffineIndex AffineCoordinateModule W affineCoordinateBasis

instance nativeFixedComplexAlgebra : Algebra ℂ (FixedPoints.subfield W NativeField) :=
  inferInstanceAs (Algebra ℂ nativeFixedField)

instance productFixedNativeAlgebra : Algebra nativeFixedField productFixedField :=
  affineFixedAlgebra NativeField AffineIndex AffineCoordinateModule W affineCoordinateBasis

instance productFixedComplexAlgebra : Algebra ℂ productFixedField :=
  ((algebraMap nativeFixedField productFixedField).comp (algebraMap ℂ nativeFixedField)).toAlgebra

instance productFixedScalarTower : IsScalarTower ℂ nativeFixedField productFixedField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance productFixedScalarTower' : IsScalarTower ℂ (FixedPoints.subfield W NativeField) productFixedField :=
  productFixedScalarTower

theorem productFixed_algebraMap_coe (c : ℂ) :
    (algebraMap ℂ productFixedField c : ProductField) = algebraMap ℂ ProductField c := by
  change algebraMap NativeField ProductField (algebraMap ℂ NativeField c) = _
  exact (IsScalarTower.algebraMap_apply ℂ NativeField ProductField c).symm

/-- The first no-name projection has been proved on the actual native
projective generic stalk, with the actual eight-coordinate affine action. -/
def firstProjectionAlgEquiv : productFixedField ≃ₐ[ℂ] Rational nativeFixedField AffineIndex :=
  (affineNoNameAlgEquiv NativeField AffineIndex AffineCoordinateModule W affineCoordinateBasis).restrictScalars ℂ

def firstProjectionEightEquiv : productFixedField ≃ₐ[ℂ] M9.RationalField nativeFixedField 8 :=
  firstProjectionAlgEquiv.trans
    ((M9.rationalFieldReindex nativeFixedField (finSumFinEquiv : (Fin 4 ⊕ Fin 4) ≃ Fin 8)).restrictScalars ℂ)

abbrev RelativeModule := ScalarExtendedRepresentation.FrameModule
abbrev RelativeProjectiveField := projectiveField AffineField RelativeModule

def splitMatrixIndex : (Fin 8 ⊕ Unit) ≃ Fin 9 :=
  (Equiv.sumCongr (Equiv.refl (Fin 8)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

@[simp] theorem splitMatrixIndex_inl (i : Fin 8) : splitMatrixIndex (Sum.inl i) = i.castSucc := rfl
@[simp] theorem splitMatrixIndex_inr : splitMatrixIndex (Sum.inr ()) = Fin.last 8 := rfl

def relativeMatrixBasis : Module.Basis (Fin 9) AffineField RelativeModule :=
  ScalarExtendedRepresentation.frameBasis.reindex ProjectiveFunctionField.matrixIndexEquiv

def relativeStandardBasis : Module.Basis (Fin 8 ⊕ Unit) AffineField RelativeModule :=
  relativeMatrixBasis.reindex splitMatrixIndex.symm

@[simp] theorem relativeStandardBasis_apply (i : Fin 8 ⊕ Unit) :
    relativeStandardBasis i = relativeMatrixBasis (splitMatrixIndex i) := by
  simp only [relativeStandardBasis, Module.Basis.coe_reindex, Function.comp_apply, Equiv.symm_symm]

instance relativeProjectiveComplexAlgebra : Algebra ℂ RelativeProjectiveField :=
  ((algebraMap AffineField RelativeProjectiveField).comp (algebraMap ℂ AffineField)).toAlgebra

instance relativeProjectiveScalarTower : IsScalarTower ℂ AffineField RelativeProjectiveField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def relativeProductAlgEquiv : ProductField ≃ₐ[ℂ] RelativeProjectiveField :=
  productChartEquiv.trans
    ((projectiveFieldEquiv AffineField (Fin 8) RelativeModule relativeStandardBasis).restrictScalars ℂ)

@[simp] theorem relativeProductAlgEquiv_affine (i : AffineIndex) :
    relativeProductAlgEquiv (algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i)) =
      algebraMap AffineField RelativeProjectiveField (PermutationInvariants.coordinate ℂ i) :=
  relativeProductRingEquiv_affine RelativeModule relativeStandardBasis i

@[simp] theorem relativeProductAlgEquiv_projective (i : Fin 8) :
    relativeProductAlgEquiv (algebraMap NativeField ProductField
      (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) =
      coordinateRatio AffineField RelativeModule (relativeMatrixBasis i.castSucc)
        (relativeMatrixBasis (Fin.last 8)) :=
  by
    change projectiveFieldEquiv AffineField (Fin 8) RelativeModule relativeStandardBasis
      (productChartEquiv _) = _
    rw [productChartEquiv_projective, projectiveFieldEquiv_variable,
      relativeStandardBasis_apply, relativeStandardBasis_apply,
      splitMatrixIndex_inl, splitMatrixIndex_inr]

theorem frameCoefficient_eq_matrix (g : W) (i j : Fin 3 × Fin 3) :
    ScalarExtendedRepresentation.frameCoefficient g i j =
      (FrameProjectiveGeometry.matrixRepresentation g⁻¹ : FrameProjectiveGeometry.Matrix9)
        (ProjectiveFunctionField.matrixIndexEquiv i) (ProjectiveFunctionField.matrixIndexEquiv j) := by
  have hs : ProjectiveFunctionField.matrixCoordinates (Matrix.stdBasis ℂ (Fin 3) (Fin 3) j) =
      Pi.single (ProjectiveFunctionField.matrixIndexEquiv j) 1 := by
    rcases j with ⟨j₁,j₂⟩
    rw [Matrix.stdBasis_eq_single]
    funext a
    simp [ProjectiveFunctionField.matrixCoordinates, Matrix.single, Pi.single_apply,
      ← Prod.mk.injEq, Equiv.eq_symm_apply, eq_comm]
  have h := congrFun (FrameProjectiveGeometry.matrixRepresentation_matrixCoordinates g⁻¹
    (Matrix.stdBasis ℂ (Fin 3) (Fin 3) j)) (ProjectiveFunctionField.matrixIndexEquiv i)
  rw [hs, Matrix.mulVec_single_one] at h
  simpa [ScalarExtendedRepresentation.frameCoefficient, ScalarExtendedRepresentation.frameDualBasis,
    Module.Basis.dualBasis_apply, ProjectiveFunctionField.matrixCoordinates,
    Matrix.stdBasis] using h.symm

theorem relativeMatrixBasis_action (g : W) (i : Fin 9) :
    g • relativeMatrixBasis i =
      ∑ j, algebraMap ℂ AffineField
        ((FrameProjectiveGeometry.matrixRepresentation g⁻¹ : FrameProjectiveGeometry.Matrix9) i j) •
          relativeMatrixBasis j := by
  simp only [relativeMatrixBasis, Module.Basis.coe_reindex, Function.comp_apply]
  rw [ScalarExtendedRepresentation.frameBasis_action_native]
  simpa only [frameCoefficient_eq_matrix, Equiv.apply_symm_apply, Equiv.symm_apply_apply, relativeMatrixBasis,
    Module.Basis.coe_reindex, Function.comp_apply] using
    (Equiv.sum_comp ProjectiveFunctionField.matrixIndexEquiv
      (fun j : Fin 9 => algebraMap ℂ AffineField
        ((FrameProjectiveGeometry.matrixRepresentation g⁻¹ : FrameProjectiveGeometry.Matrix9) i j) •
          ScalarExtendedRepresentation.frameBasis (ProjectiveFunctionField.matrixIndexEquiv.symm j)))

def normalizedPolynomialHom : FrameProjectiveGeometry.HomogeneousRing →ₐ[ℂ] MvPolynomial (Fin 8) ℂ where
  __ := (ProjectiveFunctionField.chartCoordinatesEquiv 8 (Fin.last 8)).toRingHom.comp
    (ProjectiveGeometry.Dehomogenization.dehomogenize (Fin.last 8))
  commutes' c := by simp [ProjectiveFunctionField.chartCoordinatesEquiv]

def normalizedProductMap : FrameProjectiveGeometry.HomogeneousRing →ₐ[ℂ] RelativeProjectiveField :=
  relativeProductAlgEquiv.toAlgHom.comp
    ((IsScalarTower.toAlgHom ℂ NativeField ProductField).comp
      (ProjectiveFunctionField.matrixFunctionFieldEquiv.symm.toAlgHom.comp
        ((IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8))).comp
          normalizedPolynomialHom)))

theorem normalizedProductMap_apply (f : FrameProjectiveGeometry.HomogeneousRing) :
    normalizedProductMap f = relativeProductAlgEquiv (algebraMap NativeField ProductField
      (ProjectiveFunctionField.matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8))
          (FrameProjectiveRatios.normalizedPolynomial (Fin.last 8) f)))) := rfl

theorem normalizedProductMap_X (i : Fin 9) :
    normalizedProductMap (X i) = coordinateRatio AffineField RelativeModule (relativeMatrixBasis i)
      (relativeMatrixBasis (Fin.last 8)) := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have hz : linearCoordinate AffineField RelativeModule (relativeMatrixBasis (Fin.last 8)) ≠ 0 := by
      simpa only [relativeStandardBasis_apply, splitMatrixIndex_inr] using
        basisPivot_ne_zero AffineField (Fin 8) RelativeModule relativeStandardBasis
    rw [coordinateRatio_self AffineField RelativeModule _ hz]
    change relativeProductAlgEquiv (algebraMap NativeField ProductField
      (ProjectiveFunctionField.matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8))
          (normalizedPolynomialHom (X (Fin.last 8)))))) = 1
    have hp : normalizedPolynomialHom (X (Fin.last 8)) = 1 := by
      change ProjectiveFunctionField.chartCoordinatesEquiv 8 (Fin.last 8)
        (ProjectiveGeometry.Dehomogenization.dehomogenize (Fin.last 8) (X (Fin.last 8))) = 1
      rw [ProjectiveGeometry.Dehomogenization.dehomogenize_X_self, map_one]
    rw [hp, map_one, map_one, map_one, map_one]
  · have hp : normalizedPolynomialHom (X a.castSucc) = X a := by
      change ProjectiveFunctionField.chartCoordinatesEquiv 8 (Fin.last 8)
        (ProjectiveGeometry.Dehomogenization.dehomogenize (Fin.last 8) (X a.castSucc)) = X a
      rw [ProjectiveGeometry.Dehomogenization.dehomogenize_X_of_ne _ _ (Fin.castSucc_ne_last a)]
      simp only [ProjectiveFunctionField.chartCoordinatesEquiv, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X]
      congr 1
      apply (finSuccAboveEquiv (Fin.last 8)).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      change a.castSucc = (Fin.last 8).succAbove a
      exact (Fin.succAbove_last_apply a).symm
    change relativeProductAlgEquiv (algebraMap NativeField ProductField
      (ProjectiveFunctionField.matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8))
          (normalizedPolynomialHom (X a.castSucc))))) = _
    rw [hp]
    have he : ProjectiveFunctionField.matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8)) (X a)) =
        ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) a := by
      apply ProjectiveFunctionField.matrixFunctionFieldEquiv.injective
      rw [AlgEquiv.apply_symm_apply]
      exact (ProjectiveFunctionField.functionFieldEquiv_coordinateRatio 8 (Fin.last 8) a).symm
    rw [he, relativeProductAlgEquiv_projective]

theorem normalizedProductMap_linearForms (g : W) (i : Fin 9) :
    normalizedProductMap
      (FrameProjectiveGeometry.linearForms (FrameProjectiveGeometry.matrixRepresentation g⁻¹) i) =
      coordinateRatio AffineField RelativeModule (g • relativeMatrixBasis i)
        (relativeMatrixBasis (Fin.last 8)) := by
  rw [relativeMatrixBasis_action, coordinateRatio_sum]
  simp only [FrameProjectiveGeometry.linearForms, map_sum, map_mul, normalizedProductMap_X,
    show ∀ c : ℂ, normalizedProductMap (C c) = algebraMap ℂ RelativeProjectiveField c from
      fun c => normalizedProductMap.commutes c]
  rfl

def relativeInvariantBasis : Module.Basis (Fin 8 ⊕ Unit) AffineField RelativeModule :=
  splitInvariantBasis AffineField RelativeModule W 8 ScalarExtendedRepresentation.finrank_frameModule

theorem relativeInvariantBasis_fixed (g : W) (i : Fin 8 ⊕ Unit) :
    g • relativeInvariantBasis i = relativeInvariantBasis i :=
  splitInvariantBasis_fixed AffineField RelativeModule W 8
    ScalarExtendedRepresentation.finrank_frameModule g i

@[instance_reducible] def relativeAction : MulSemiringAction W RelativeProjectiveField :=
  projectiveAction AffineField (Fin 8) RelativeModule W relativeInvariantBasis relativeInvariantBasis_fixed

theorem relativeAction_coefficient (g : W) (a : AffineField) :
    letI := relativeAction
    g • algebraMap AffineField RelativeProjectiveField a =
      algebraMap AffineField RelativeProjectiveField (g • a) := by
  let := FiniteNoNameField.symmetricRationalAction W AffineField RelativeModule relativeInvariantBasis
  apply Subtype.ext
  change g • algebraMap AffineField (CoordinateField AffineField RelativeModule) a = _
  rw [FiniteNoNameField.symmetricRationalAction_constant]
  rfl

theorem relativeProductAlgEquiv_nativeAction (g : W) (i : Fin 8) :
    letI := productAction
    letI := relativeAction
    relativeProductAlgEquiv
      (g • algebraMap NativeField ProductField (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) =
      g • relativeProductAlgEquiv
        (algebraMap NativeField ProductField (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) := by
  let := productAction
  let := relativeAction
  rw [productAction_coefficient, relativeProductAlgEquiv_projective]
  rw [projectiveAction_coordinateRatio AffineField (Fin 8) RelativeModule W
    relativeInvariantBasis relativeInvariantBasis_fixed]
  have hn : g • ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i =
      ProjectiveFunctionField.matrixFunctionFieldEquiv.symm
        (algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8))
          (FrameProjectiveRatios.normalizedPolynomial (Fin.last 8)
            (FrameProjectiveGeometry.linearForms (FrameProjectiveGeometry.matrixRepresentation g⁻¹) i.castSucc)) /
        algebraMap (MvPolynomial (Fin 8) ℂ) (Rational ℂ (Fin 8))
          (FrameProjectiveRatios.normalizedPolynomial (Fin.last 8)
            (FrameProjectiveGeometry.linearForms (FrameProjectiveGeometry.matrixRepresentation g⁻¹) (Fin.last 8)))) := by
    apply ProjectiveFunctionField.matrixFunctionFieldEquiv.injective
    rw [AlgEquiv.apply_symm_apply]
    change ProjectiveFunctionField.functionFieldEquiv 8 (Fin.last 8)
      (FrameProjectiveGeometry.fieldRepresentation g
        (ProjectiveFunctionField.coordinateRatio 8 (Fin.last 8) i)) = _
    simpa only [finSuccAboveEquiv_apply, Fin.succAbove_last] using
      FrameProjectiveRatios.functionFieldEquiv_fieldRepresentation_coordinateRatio g (Fin.last 8) i
  rw [hn, map_div₀, map_div₀, map_div₀]
  change normalizedProductMap
      (FrameProjectiveGeometry.linearForms (FrameProjectiveGeometry.matrixRepresentation g⁻¹) i.castSucc) /
    normalizedProductMap
      (FrameProjectiveGeometry.linearForms (FrameProjectiveGeometry.matrixRepresentation g⁻¹) (Fin.last 8)) = _
  rw [normalizedProductMap_linearForms, normalizedProductMap_linearForms]
  have hz : linearCoordinate AffineField RelativeModule (relativeMatrixBasis (Fin.last 8)) ≠ 0 := by
    simpa only [relativeStandardBasis_apply, splitMatrixIndex_inr] using
      basisPivot_ne_zero AffineField (Fin 8) RelativeModule relativeStandardBasis
  exact (coordinateRatio_div AffineField RelativeModule _ _ _ hz).symm

/-- The explicit product-field isomorphism intertwines the original
native projective frame action and the genuine scalar-extended
contragredient action. No invariant-field comparison is an input. -/
theorem relativeProductAlgEquiv_smul (g : W) (x : ProductField) :
    letI := productAction
    letI := relativeAction
    relativeProductAlgEquiv (g • x) = g • relativeProductAlgEquiv x := by
  let := productAction
  let := relativeAction
  have hh : relativeProductAlgEquiv.toRingHom.comp (MulSemiringAction.toRingHom W ProductField g) =
      (MulSemiringAction.toRingHom W RelativeProjectiveField g).comp relativeProductAlgEquiv.toRingHom := by
    apply productRingHom_ext
    · intro c
      change relativeProductAlgEquiv (g • algebraMap ℂ ProductField c) =
        g • relativeProductAlgEquiv (algebraMap ℂ ProductField c)
      rw [relativeProductAlgEquiv.commutes]
      have hp : g • algebraMap ℂ ProductField c = algebraMap ℂ ProductField c := by
        rw [IsScalarTower.algebraMap_apply ℂ NativeField ProductField, productAction_coefficient,
          smul_algebraMap]
      have hr : g • algebraMap ℂ RelativeProjectiveField c = algebraMap ℂ RelativeProjectiveField c := by
        rw [IsScalarTower.algebraMap_apply ℂ AffineField RelativeProjectiveField,
          relativeAction_coefficient, smul_algebraMap]
      rw [hp, hr, relativeProductAlgEquiv.commutes]
    · intro i
      change relativeProductAlgEquiv
        (g • algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i)) =
        g • relativeProductAlgEquiv (algebraMap (MvPolynomial AffineIndex NativeField) ProductField (X i))
      rw [productAction_affine, relativeProductAlgEquiv_affine, relativeProductAlgEquiv_affine,
        relativeAction_coefficient, WreathFrameComparison.frame_smul_coordinate]
    · exact relativeProductAlgEquiv_nativeAction g
  exact RingHom.congr_fun hh x

abbrev relativeFixedField : Subfield RelativeProjectiveField :=
  projectiveFixedField AffineField (Fin 8) RelativeModule W relativeInvariantBasis relativeInvariantBasis_fixed

abbrev AffineFixedField := WreathFrameComparison.frameFixedField ℂ

instance affineFixedComplexAlgebra : Algebra ℂ (FixedPoints.subfield W AffineField) :=
  inferInstanceAs (Algebra ℂ AffineFixedField)

instance relativeFixedAffineAlgebra : Algebra AffineFixedField relativeFixedField :=
  projectiveFixedAlgebra AffineField (Fin 8) RelativeModule W relativeInvariantBasis relativeInvariantBasis_fixed

instance relativeFixedComplexAlgebra : Algebra ℂ relativeFixedField :=
  ((algebraMap AffineFixedField relativeFixedField).comp (algebraMap ℂ AffineFixedField)).toAlgebra

instance relativeFixedScalarTower : IsScalarTower ℂ AffineFixedField relativeFixedField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance relativeFixedScalarTower' : IsScalarTower ℂ (FixedPoints.subfield W AffineField) relativeFixedField :=
  relativeFixedScalarTower

theorem relativeFixed_algebraMap_coe (c : ℂ) :
    (algebraMap ℂ relativeFixedField c : RelativeProjectiveField) =
      algebraMap ℂ RelativeProjectiveField c := by
  change algebraMap AffineField RelativeProjectiveField (algebraMap ℂ AffineField c) = _
  exact (IsScalarTower.algebraMap_apply ℂ AffineField RelativeProjectiveField c).symm

/-- Equivariance restricts the explicit product isomorphism to the actual
fixed subfields on both sides. -/
def productFixedToRelativeFixedEquiv : productFixedField ≃ₐ[ℂ] relativeFixedField := by
  let := productAction
  let := relativeAction
  exact
  { __ := fixedFieldEquivOfEquivariant W relativeProductAlgEquiv.toRingEquiv relativeProductAlgEquiv_smul
    commutes' := fun c => by
      apply Subtype.ext
      change relativeProductAlgEquiv (algebraMap ℂ productFixedField c : ProductField) =
        (algebraMap ℂ relativeFixedField c : RelativeProjectiveField)
      rw [productFixed_algebraMap_coe, relativeFixed_algebraMap_coe]
      exact relativeProductAlgEquiv.commutes c }

/-- The second projection is genuinely rational of dimension sixteen:
projective no-name contributes eight variables over the actual rational
eight-dimensional permutation invariant field. -/
def secondProjectionRationalEquiv : relativeFixedField ≃ₐ[ℂ] M9.RationalField ℂ 16 :=
  (((projectiveFixedFieldAlgEquiv AffineField (Fin 8) RelativeModule W relativeInvariantBasis
      relativeInvariantBasis_fixed).symm.restrictScalars ℂ).trans
    (rationalCoefficientEquiv ℂ (Fin 8) (WreathFrameComparison.frameFixedFieldEquiv ℂ))).trans
      (M9.rationalFieldIteratedEquiv ℂ 8 8)

/-- The actual native projective invariant field becomes rational after
adjoining eight independent variables. This is the two-projection
finite no-name comparison used for the frame quotient. -/
def stableProjectiveInvariantEquiv :
    M9.RationalField nativeFixedField 8 ≃ₐ[ℂ] M9.RationalField ℂ 16 :=
  firstProjectionEightEquiv.symm.trans
    (productFixedToRelativeFixedEquiv.trans secondProjectionRationalEquiv)

theorem nativeFixedField_stablyRational :
    Nonempty (M9.RationalField nativeFixedField 8 ≃ₐ[ℂ] M9.RationalField ℂ 16) :=
  ⟨stableProjectiveInvariantEquiv⟩

end Concrete

end M9.ProjectiveNoName

module

public import M9StacksIntegration.ProjectivePairSLFixedField
public import M9StacksIntegration.PairProjectiveEquivariance
public import M9StacksIntegration.CoefficientRationalDescent
public import M9.GraphBundleDescent

/-! The literal connected SL3 quotient of the actual conic-frame coefficient
field, retaining all sixteen independent raw fibre variables. The group is
not assumed finite; coefficient descent applies to the actual native SL3.
The deck comparisons below concern coefficient embeddings only. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open MvPolynomial
open scoped Classical

namespace M9Native.ConicFramedSLQuotient

open M9.GraphBundleDescent M9.FiniteNoNameField
open M9.ProjectiveFrameQuotient M9.FrameQuotientActionComparison M9.FrameProjectiveGeometry
open ProjectivePairSLFixedField

abbrev B := projectivePairField
abbrev Q := NativeMatrixField
abbrev M := FractionRing (MvPolynomial FiberIndex B)
abbrev QuotientField := FractionRing (MvPolynomial FiberIndex Q)

attribute [local instance] ProjectivePairSLFixedField.slAction

local instance framedAction : MulSemiringAction SL3 M :=
  M9.FiniteNoNameField.rationalAction (G := SL3) (L := B) (ι := FiberIndex)

/-- The coefficient-only action of the actual original SL3 matrices. -/
def coefficientTranslate (g : SL3) : M →+* M :=
  @MulSemiringAction.toRingHom SL3 inferInstance M inferInstance framedAction g

/-- The genuine connected quotient inclusion, with its original values. -/
def coefficientEmbedding : Q →ₐ[ℂ] B :=
  slFixedField.val.comp nativeSLQuotientEquiv.toAlgHom

@[simp] theorem coefficientEmbedding_val (x : Q) :
    coefficientEmbedding x = (nativeSLQuotientEquiv x).val := rfl

/-- No new field identification: this is the existing actual SL3 quotient. -/
def coefficientFixedEquiv : Q ≃+* FixedField SL3 B :=
  nativeSLQuotientEquiv.toRingEquiv

def polynomialEmbedding : MvPolynomial FiberIndex Q →ₐ[ℂ] MvPolynomial FiberIndex B :=
  MvPolynomial.mapAlgHom coefficientEmbedding

def polynomialToField : MvPolynomial FiberIndex Q →ₐ[ℂ] M :=
  (IsScalarTower.toAlgHom ℂ (MvPolynomial FiberIndex B) M).comp polynomialEmbedding

theorem polynomialToField_injective : Function.Injective polynomialToField :=
  (IsFractionRing.injective (MvPolynomial FiberIndex B) M).comp
    (MvPolynomial.map_injective _ coefficientEmbedding.injective)

/-- The literal inclusion of the native projective matrix field with the
same sixteen independent raw variables. -/
def quotientEmbedding : QuotientField →ₐ[ℂ] M :=
  IsFractionRing.liftAlgHom (g := polynomialToField) polynomialToField_injective

theorem quotientEmbedding_polynomial (p : MvPolynomial FiberIndex Q) :
    quotientEmbedding (algebraMap _ QuotientField p) = polynomialToField p :=
  IsFractionRing.lift_algebraMap polynomialToField_injective p

local instance fixedFractionCommRing :
    CommRing (FractionRing (MvPolynomial FiberIndex (FixedField SL3 B))) := inferInstance

local instance fixedPolynomialSelfDistribMulAction :
    DistribMulAction (MvPolynomial FiberIndex (FixedField SL3 B))
      (MvPolynomial FiberIndex (FixedField SL3 B)) where
  smul a b := a * b
  one_smul := one_mul
  mul_smul := mul_assoc
  smul_zero := mul_zero
  smul_add := mul_add

def coefficientFractionEquiv : QuotientField ≃+*
    FractionRing (MvPolynomial FiberIndex (FixedField SL3 B)) :=
  IsFractionRing.ringEquivOfRingEquiv
    (A := MvPolynomial FiberIndex Q)
    (B := MvPolynomial FiberIndex (FixedField SL3 B))
    (K := QuotientField)
    (L := FractionRing (MvPolynomial FiberIndex (FixedField SL3 B)))
    (MvPolynomial.mapEquiv FiberIndex coefficientFixedEquiv)

theorem quotientEmbedding_eq_include (f : QuotientField) :
    quotientEmbedding f = rationalInclude SL3 B FiberIndex (coefficientFractionEquiv f) := by
  have hh : quotientEmbedding.toRingHom =
      (rationalInclude SL3 B FiberIndex).comp coefficientFractionEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial FiberIndex Q)
    intro p
    change quotientEmbedding (algebraMap _ QuotientField p) =
      rationalInclude SL3 B FiberIndex (coefficientFractionEquiv
        (algebraMap _ QuotientField p))
    rw [quotientEmbedding_polynomial]
    unfold coefficientFractionEquiv
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, rationalInclude_polynomial]
    change algebraMap (MvPolynomial FiberIndex B) M
        (MvPolynomial.map coefficientEmbedding.toRingHom p) =
      algebraMap (MvPolynomial FiberIndex B) M
        (MvPolynomial.map (FixedField SL3 B).subtype
          (MvPolynomial.map coefficientFixedEquiv.toRingHom p))
    congr 1
    rw [MvPolynomial.map_map]
    congr 1
  exact DFunLike.congr_fun hh f

/-- Fixed image for the actual infinite native SL3, without a finiteness
hypothesis or an assumed quotient-field equality. -/
theorem quotientEmbedding_image_iff (f : M) :
    (∃ x : QuotientField, quotientEmbedding x = f) ↔
      ∀ g : SL3, coefficientTranslate g f = f := by
  have hd := CoefficientRationalDescent.fixed_rational_iff_descends SL3 B FiberIndex f
  change (∀ g : SL3, coefficientTranslate g f = f) ↔ _ at hd
  rw [hd]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨coefficientFractionEquiv x,(quotientEmbedding_eq_include x).symm.trans hx⟩
  · rintro ⟨x,hx⟩
    refine ⟨coefficientFractionEquiv.symm x, ?_⟩
    exact (quotientEmbedding_eq_include _).trans
      ((congrArg (rationalInclude SL3 B FiberIndex)
        (coefficientFractionEquiv.apply_symm_apply x)).trans hx)

theorem quotientEmbedding_variable (ij : FiberIndex) :
    quotientEmbedding (algebraMap (MvPolynomial FiberIndex Q) QuotientField (X ij)) =
      algebraMap (MvPolynomial FiberIndex B) M (X ij) := by
  rw [quotientEmbedding_polynomial]
  change algebraMap (MvPolynomial FiberIndex B) M
    (MvPolynomial.map coefficientEmbedding.toRingHom (X ij)) = _
  rw [MvPolynomial.map_X]

theorem quotientEmbedding_constant (x : Q) :
    quotientEmbedding (algebraMap Q QuotientField x) =
      algebraMap B M (coefficientEmbedding x) := by
  change quotientEmbedding (algebraMap (MvPolynomial FiberIndex Q) QuotientField (C x)) = _
  rw [quotientEmbedding_polynomial]
  change algebraMap (MvPolynomial FiberIndex B) M
    (MvPolynomial.map coefficientEmbedding.toRingHom (C x)) = _
  rw [MvPolynomial.map_C]
  exact (IsScalarTower.algebraMap_apply B (MvPolynomial FiberIndex B) M _).symm

theorem coefficientTranslate_constant (g : SL3) (x : B) :
    coefficientTranslate g (algebraMap B M x) =
      algebraMap B M (slActionHom g x) := by
  exact rationalAction_constant SL3 B FiberIndex g x

theorem coefficientTranslate_variable (g : SL3) (ij : FiberIndex) :
    coefficientTranslate g (algebraMap (MvPolynomial FiberIndex B) M (X ij)) =
      algebraMap (MvPolynomial FiberIndex B) M (X ij) := by
  exact rationalAction_variable SL3 B FiberIndex g ij

/-- Original wreath deck, retaining both original coefficient inclusions. -/
theorem coefficientEmbedding_ambient_deck (w : M9.FrameQuotientActionComparison.W) (x : Q) :
    deckOperator w ((coefficientEmbedding x : B) : PF) =
      ((coefficientEmbedding (fieldRepresentation w x) : B) : PF) := by
  change deckOperator w (projectiveInvariantEmbedding x) =
    projectiveInvariantEmbedding (fieldRepresentation w x)
  exact deckOperator_embedding w x

/-- Literal independent tetrahedral right decks on coefficients. -/
theorem coefficientEmbedding_pairDeck (a b : Gamma) (x : Q) :
    PairProjectiveEquivariance.projectivePairDeck a b (coefficientEmbedding x) =
      coefficientEmbedding (fieldRepresentation (M9.FrameAction.FrameGroup.pairHom (a,b)) x) := by
  apply Subtype.ext
  change pairDeck a b (projectiveInvariantEmbedding x) =
    projectiveInvariantEmbedding (fieldRepresentation (M9.FrameAction.FrameGroup.pairHom (a,b)) x)
  exact pairDeck_embedding a b x

/-- Literal swap on coefficients; no raw fibre action is asserted here. -/
theorem coefficientEmbedding_pairSwap (x : Q) :
    PairProjectiveEquivariance.projectivePairSwap (coefficientEmbedding x) =
      coefficientEmbedding (fieldRepresentation M9.FrameAction.FrameGroup.tau x) := by
  apply Subtype.ext
  change pairSwap (projectiveInvariantEmbedding x) =
    projectiveInvariantEmbedding (fieldRepresentation M9.FrameAction.FrameGroup.tau x)
  exact pairSwap_embedding x

end M9Native.ConicFramedSLQuotient

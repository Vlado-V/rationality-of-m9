module

public import M9StacksIntegration.ConicGraphBaseCoordinates
public import M9StacksIntegration.CoefficientRationalDescent

/-! Exact coefficient descent of the actual sixteen-base/sixteen-fibre graph
field along the actual independent conic-frame cover. This is a literal
coordinate inclusion; its fixed image is proved from the actual base-cover
fixed-field theorem and genuine rational coefficient descent. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open MvPolynomial
open scoped Classical

namespace M9Native.ConicGraphCoefficientDescent

open M9.GraphBundleDescent M9.FiniteNoNameField
open ConicGraphBaseCoordinates

abbrev G := M9.TetrahedralGroup.Gamma × M9.TetrahedralGroup.Gamma
abbrev B := ConicGraphBaseCoordinates.FrameField
abbrev M := FractionRing (MvPolynomial FiberIndex B)

def frameRepresentation : G →* (B ≃ₐ[ℂ] B) :=
  (AlgEquiv.autCongr PairProjectiveRatios.pairProjectiveEquiv).toMonoidHom.comp
    ConicFrameIndependentPairAction.pairRepresentation

theorem frameRepresentation_apply (g : G) (z : B) :
    frameRepresentation g z = PairProjectiveEquivariance.projectivePairDeck g.1 g.2 z := by
  have h := PairProjectiveEquivariance.pairProjectiveEquiv_pairDeck g.1 g.2
    (PairProjectiveRatios.pairProjectiveEquiv.symm z)
  change PairProjectiveRatios.pairProjectiveEquiv
    (ConicFrameIndependentPairAction.pairRepresentation g
      (PairProjectiveRatios.pairProjectiveEquiv.symm z)) = _
  simpa only [Prod.mk.eta, AlgEquiv.apply_symm_apply] using h

@[instance_reducible] def frameAction : MulSemiringAction G B :=
  MulSemiringAction.compHom B frameRepresentation

attribute [local instance] frameAction

local instance coefficientAction : MulSemiringAction G M :=
  M9.FiniteNoNameField.rationalAction (G := G) (L := B) (ι := FiberIndex)

/-- The actual coefficient action, with its already constructed instance pinned. -/
def coefficientTranslate (g : G) : M →+* M :=
  @MulSemiringAction.toRingHom G inferInstance M inferInstance coefficientAction g

def baseToFixed : BaseFunctionField ℂ →+* FixedField G B where
  toFun z := ⟨baseEmbedding z, by
    intro g
    change frameRepresentation g (baseEmbedding z) = baseEmbedding z
    exact (frameRepresentation_apply g (baseEmbedding z)).trans
      (baseEmbedding_deck_fixed g.1 g.2 z)⟩
  map_zero' := Subtype.ext (map_zero baseEmbedding)
  map_one' := Subtype.ext (map_one baseEmbedding)
  map_add' x y := Subtype.ext (map_add baseEmbedding x y)
  map_mul' x y := Subtype.ext (map_mul baseEmbedding x y)

theorem baseToFixed_surjective : Function.Surjective baseToFixed := by
  intro z
  obtain ⟨x,hx⟩ := exists_baseEmbedding z.val (fun a b => by
    have h := z.property (a,b)
    change frameRepresentation (a,b) z.val = z.val at h
    exact (frameRepresentation_apply (a,b) z.val).symm.trans h)
  exact ⟨x,Subtype.ext hx⟩

def baseFixedEquiv : BaseFunctionField ℂ ≃+* FixedField G B :=
  RingEquiv.ofBijective baseToFixed ⟨baseToFixed.injective,baseToFixed_surjective⟩

def polynomialEmbedding : MvPolynomial FiberIndex (BaseFunctionField ℂ) →ₐ[ℂ]
    MvPolynomial FiberIndex B :=
  MvPolynomial.mapAlgHom baseEmbedding

def polynomialToField : MvPolynomial FiberIndex (BaseFunctionField ℂ) →ₐ[ℂ] M :=
  (IsScalarTower.toAlgHom ℂ (MvPolynomial FiberIndex B) M).comp polynomialEmbedding

theorem polynomialToField_injective : Function.Injective polynomialToField :=
  (IsFractionRing.injective (MvPolynomial FiberIndex B) M).comp
    (MvPolynomial.map_injective _ baseEmbedding.injective)

/-- The literal sixteen-variable coefficient inclusion along the actual
native base conic pullback. -/
def relativeEmbedding : RelativeFunctionField ℂ →ₐ[ℂ] M :=
  IsFractionRing.liftAlgHom (g := polynomialToField) polynomialToField_injective

theorem relativeEmbedding_polynomial (p : MvPolynomial FiberIndex (BaseFunctionField ℂ)) :
    relativeEmbedding (algebraMap _ (RelativeFunctionField ℂ) p) = polynomialToField p :=
  IsFractionRing.lift_algebraMap polynomialToField_injective p

local instance fixedFractionCommRing :
    CommRing (FractionRing (MvPolynomial FiberIndex (FixedField G B))) := inferInstance

local instance frameFractionCommRing : CommRing M := inferInstance

-- Pin the usual self-scalar action (ordinary multiplication) before
-- elaborating the fixed-coefficient localization. No ring operation changes.
local instance fixedPolynomialSelfDistribMulAction :
    DistribMulAction (MvPolynomial FiberIndex (FixedField G B))
      (MvPolynomial FiberIndex (FixedField G B)) where
  smul a b := a * b
  one_smul := one_mul
  mul_smul := mul_assoc
  smul_zero := mul_zero
  smul_add := mul_add

def baseCoefficientEquiv : RelativeFunctionField ℂ ≃+*
    FractionRing (MvPolynomial FiberIndex (FixedField G B)) :=
  IsFractionRing.ringEquivOfRingEquiv
    (A := MvPolynomial FiberIndex (BaseFunctionField ℂ))
    (B := MvPolynomial FiberIndex (FixedField G B))
    (K := RelativeFunctionField ℂ)
    (L := FractionRing (MvPolynomial FiberIndex (FixedField G B)))
    (MvPolynomial.mapEquiv FiberIndex baseFixedEquiv)

theorem relativeEmbedding_eq_include (f : RelativeFunctionField ℂ) :
    relativeEmbedding f = rationalInclude G B FiberIndex (baseCoefficientEquiv f) := by
  have hh : relativeEmbedding.toRingHom =
      (rationalInclude G B FiberIndex).comp baseCoefficientEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial FiberIndex (BaseFunctionField ℂ))
    intro p
    change relativeEmbedding (algebraMap _ (RelativeFunctionField ℂ) p) =
      rationalInclude G B FiberIndex (baseCoefficientEquiv
        (algebraMap _ (RelativeFunctionField ℂ) p))
    rw [relativeEmbedding_polynomial]
    unfold baseCoefficientEquiv
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, rationalInclude_polynomial]
    change algebraMap (MvPolynomial FiberIndex B) M (MvPolynomial.map baseEmbedding.toRingHom p) =
      algebraMap (MvPolynomial FiberIndex B) M
        (MvPolynomial.map (FixedField G B).subtype (MvPolynomial.map baseFixedEquiv.toRingHom p))
    congr 1
    rw [MvPolynomial.map_map]
    congr 1
  exact DFunLike.congr_fun hh f

/-- Exact image, with all independent rational coordinates retained. -/
theorem relativeEmbedding_image_iff (f : M) :
    (∃ x : RelativeFunctionField ℂ, relativeEmbedding x = f) ↔ ∀ g : G, coefficientTranslate g f = f := by
  have hd := CoefficientRationalDescent.fixed_rational_iff_descends G B FiberIndex f
  change (∀ g : G, coefficientTranslate g f = f) ↔ _ at hd
  rw [hd]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨baseCoefficientEquiv x,(relativeEmbedding_eq_include x).symm.trans hx⟩
  · rintro ⟨x,hx⟩
    refine ⟨baseCoefficientEquiv.symm x, ?_⟩
    exact (relativeEmbedding_eq_include _).trans
      ((congrArg (rationalInclude G B FiberIndex) (baseCoefficientEquiv.apply_symm_apply x)).trans hx)

/-- The exact native graph coordinate field, split by its proved original
base/fibre polynomial equivalence. -/
def chartEmbedding : ChartFunctionField ℂ →ₐ[ℂ] M :=
  relativeEmbedding.comp (chartRelativeEquiv ℂ).toAlgHom

theorem chartEmbedding_image_iff (f : M) :
    (∃ x : ChartFunctionField ℂ, chartEmbedding x = f) ↔ ∀ g : G, coefficientTranslate g f = f := by
  rw [← relativeEmbedding_image_iff f]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨chartRelativeEquiv ℂ x,hx⟩
  · rintro ⟨x,hx⟩
    refine ⟨(chartRelativeEquiv ℂ).symm x, ?_⟩
    change relativeEmbedding (chartRelativeEquiv ℂ ((chartRelativeEquiv ℂ).symm x)) = f
    rw [AlgEquiv.apply_symm_apply]
    exact hx

theorem chartEmbedding_fiber (ij : FiberIndex) :
    chartEmbedding (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (.inr ij))) =
      algebraMap (MvPolynomial FiberIndex B) M (X ij) := by
  change relativeEmbedding (chartRelativeEquiv ℂ _) = _
  rw [chartRelativeEquiv_fiber_coordinate, relativeEmbedding_polynomial]
  change algebraMap (MvPolynomial FiberIndex B) M (MvPolynomial.map baseEmbedding.toRingHom (X ij)) = _
  rw [MvPolynomial.map_X]

theorem chartEmbedding_base (b : BaseIndex) :
    chartEmbedding (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (.inl b))) =
      algebraMap B M (baseEmbedding
        (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X b))) := by
  change relativeEmbedding (chartRelativeEquiv ℂ _) = _
  rw [chartRelativeEquiv_base_coordinate]
  change relativeEmbedding (algebraMap (MvPolynomial FiberIndex (BaseFunctionField ℂ))
    (RelativeFunctionField ℂ)
      (C (algebraMap (MvPolynomial BaseIndex ℂ) (BaseFunctionField ℂ) (X b)))) = _
  rw [relativeEmbedding_polynomial]
  simp only [polynomialToField, AlgHom.comp_apply, polynomialEmbedding,
    MvPolynomial.mapAlgHom_apply, MvPolynomial.map_C, IsScalarTower.toAlgHom_apply]
  exact (IsScalarTower.algebraMap_apply B (MvPolynomial FiberIndex B) M _).symm

end M9Native.ConicGraphCoefficientDescent

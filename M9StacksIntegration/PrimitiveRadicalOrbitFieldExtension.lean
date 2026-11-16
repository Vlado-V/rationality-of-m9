module

public import M9StacksIntegration.PrimitiveRadicalOrbitDominance

/-! The genuine native source function field is algebraic over the native Grassmannian
function field through the actual dominant-family pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

namespace M9Native.PrimitiveRadicalOrbitFieldExtension

abbrev targetField := (GrassmannianCharts.space ℂ 9 14).functionField
abbrev sourceField := PrimitiveRadicalOrbitFamily.source.functionField

/-- Exactly the algebra structure induced by the genuine native orbit-family pullback. -/
instance fieldAlgebra : Algebra targetField sourceField :=
  PrimitiveRadicalOrbitDominance.functionFieldEmbedding.toRingHom.toAlgebra

instance fieldTower : IsScalarTower ℂ targetField sourceField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact PrimitiveRadicalOrbitDominance.functionFieldEmbedding.comp_algebraMap.symm

@[simp] theorem algebraMap_apply (x : targetField) : algebraMap targetField sourceField x =
    PrimitiveRadicalOrbitDominance.functionFieldEmbedding x := rfl

theorem target_trdeg : Algebra.trdeg ℂ targetField = 45 := by
  rw [(GrassmannianCharts.rationalFunctionFieldEquiv ℂ 9 14).trdeg_eq]
  have : Algebra.IsAlgebraic (MvPolynomial (Fin 45) ℂ)
      (FractionRing (MvPolynomial (Fin 45) ℂ)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin 45) ℂ))
  have h := trdeg_add_eq ℂ (MvPolynomial (Fin 45) ℂ)
    (A := FractionRing (MvPolynomial (Fin 45) ℂ))
  rw [trdeg_eq_zero (R := MvPolynomial (Fin 45) ℂ),add_zero] at h
  rw [← h]
  simp [MvPolynomial.trdeg_of_isDomain]

theorem source_trdeg : Algebra.trdeg ℂ sourceField = 45 := by
  rw [PrimitiveRadicalOrbitRings.sourceFractionEquiv.trdeg_eq]
  exact PrimitiveRadicalOrbitDominance.sourceField_trdeg

/-- Algebraicity concerns the actual generic stalks with the actual scheme-induced embedding,
not an independently chosen identification of two rational fields. -/
theorem source_isAlgebraic : Algebra.IsAlgebraic targetField sourceField :=
  GenericEtaleFibreDegree.isAlgebraic_of_equal_finite_trdeg ℂ targetField sourceField
    (by rw [target_trdeg]; exact Cardinal.ofNat_lt_aleph0)
    (by rw [target_trdeg,source_trdeg])

end M9Native.PrimitiveRadicalOrbitFieldExtension

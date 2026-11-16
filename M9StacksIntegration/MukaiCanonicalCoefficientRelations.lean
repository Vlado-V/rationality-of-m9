module

public import M9StacksIntegration.MukaiLinearSectionContainment
public import M9StacksIntegration.MukaiConormalOriginCoordinates
public import M9StacksIntegration.LagrangianSectionCoefficientCovariance
public import M9StacksIntegration.LagrangianRowPrefixes
public import M9StacksIntegration.LagrangianIncidencePlaneIso
public import M9StacksIntegration.LagrangianHyperplaneRows

/-!
# Original coefficient relations are actual primitive-evaluation relations

The original finite fourteen coefficients are identified with the true
dual primitive basis, then with the actual canonical evaluation and the
actual pulled determinant section. Both directions retain the original
field scalar action. These are actual map identities, not an assumed
kernel or conormal-image identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open scoped BigOperators
universe u

namespace M9Native.MukaiCanonicalCoefficientRelations

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation MukaiLinearSectionContainment
open MukaiConormalOriginCoordinates LagrangianPluckerQuotient

variable {X : Scheme.{u}} (K : Type u) [Field K] [CharZero K]
  (f : X ⟶ Spec (.of K)) [IsProper f] (E : X.Modules)
  (b : Basis (Fin 6) K (H0 K f E))
  (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)

/-- The original coefficient map is actual canonical evaluation of the
true dual primitive form with those very coordinates. -/
theorem coordinateEvaluation_eq (v : Fin 14 → K) :
    coordinateCanonicalEvaluation K f E b c v =
      canonicalEvaluation K f E b c ((formsCoordinates K).symm v) := by
  let B := (LagrangianPluckerLinear.primitiveBasis14 K).dualBasis
  have hrepr (j : Fin 14) : B.repr ((formsCoordinates K).symm v) j = v j := by
    change formsCoordinates K ((formsCoordinates K).symm v) j = v j
    rw [LinearEquiv.apply_symm_apply]
  have hs : (formsCoordinates K).symm v = ∑ j : Fin 14, v j • B j := by
    simpa only [hrepr] using (B.sum_repr ((formsCoordinates K).symm v)).symm
  rw [coordinateCanonicalEvaluation_apply, hs, map_sum]
  simp only [map_smul, B]

variable (d : EvaluationDiagram K f E b)

/-- The actual canonical line isomorphism takes each pulled original
row to the actual H0 image of its original coefficient relation. -/
theorem canonicalIso_pullback_determinantSection (v : Fin 14 → K) :
    (d.canonicalIso K f E c).hom.app ⊤
      (pullbackGlobalSections d.map (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K v)) =
      (cohomologyOverFieldZeroLinearIso K f (Stacks.Duality.dualizingSheafOverField f)).hom
        (coordinateCanonicalEvaluation K f E b c v) := by
  have hκ : LagrangianPlucker.coefficientMap K d.map = ExteriorEvaluation.baseRingMap K f := by
    change LagrangianParameterRowComparison.scalarMap K
      (d.map ≫ LagrangianGrassmannian.projection K) = _
    exact d.coefficients K f E
  have hscalar (a : K)
      (s : cohomologyOverField K f (Stacks.Duality.dualizingSheafOverField f) 0) :
      (cohomologyOverFieldZeroLinearIso K f (Stacks.Duality.dualizingSheafOverField f)).hom
          (a • s) = ExteriorEvaluation.baseRingMap K f a •
        (cohomologyOverFieldZeroLinearIso K f (Stacks.Duality.dualizingSheafOverField f)).hom s :=
    (cohomologyOverFieldZeroLinearIso K f
      (Stacks.Duality.dualizingSheafOverField f)).hom.hom.map_smul a s
  rw [LagrangianSectionCoefficientCovariance.determinantSection_pullback,
    coordinateCanonicalEvaluation_apply, map_sum, map_sum]
  simp only [Scheme.Modules.Hom.app_smul, hκ, d.canonicalCoordinates K f E c, hscalar]

/-- Vanishing of an actual pulled original row and of its actual
canonical coefficient relation are equivalent in both directions. -/
theorem coordinateEvaluation_zero_iff_pullback (v : Fin 14 → K) :
    coordinateCanonicalEvaluation K f E b c v = 0 ↔
      pullbackGlobalSections d.map (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K v) = 0 := by
  constructor
  · intro hv
    apply (ConcreteCategory.bijective_of_isIso ((d.canonicalIso K f E c).hom.app ⊤)).injective
    rw [canonicalIso_pullback_determinantSection, hv, map_zero, map_zero]
  · intro hv
    apply (ConcreteCategory.bijective_of_isIso
      (cohomologyOverFieldZeroLinearIso K f (Stacks.Duality.dualizingSheafOverField f)).hom).injective
    rw [← canonicalIso_pullback_determinantSection K f E b c d v, hv, map_zero, map_zero]

/-- An actual coefficient relation is a relation for the original
primitive evaluation, with the true primitive dual form and no pairing
or kernel identification supplied as an input. -/
theorem primitiveEvaluation_zero_of_relation (v : Fin 14 → K)
    (hv : coordinateCanonicalEvaluation K f E b c v = 0) :
    primitiveEvaluation K f E b ((formsCoordinates K).symm v) = 0 := by
  have hleft : cohomologyOverFieldMap K f c.hom 0 ≫
      cohomologyOverFieldMap K f c.inv 0 = 𝟙 _ := by
    rw [← cohomologyOverFieldMap_comp, c.hom_inv_id, cohomologyOverFieldMap_id]
  have hright : cohomologyOverFieldMap K f c.inv 0 ≫
      cohomologyOverFieldMap K f c.hom 0 = 𝟙 _ := by
    rw [← cohomologyOverFieldMap_comp, c.inv_hom_id, cohomologyOverFieldMap_id]
  haveI : IsIso (cohomologyOverFieldMap K f c.hom 0) :=
    ⟨⟨cohomologyOverFieldMap K f c.inv 0, hleft, hright⟩⟩
  apply (ConcreteCategory.bijective_of_isIso (cohomologyOverFieldMap K f c.hom 0)).injective
  have h := (coordinateEvaluation_eq K f E b c v).symm.trans hv
  simpa only [canonicalEvaluation, transportedEvaluation, LinearMap.comp_apply,
    map_zero] using h

/-- Original row independence is derived from the actual surjective
five-row matrix, without a row-injection premise. -/
theorem rowCombination_injective (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) :
    Function.Injective (fun a : Fin 5 → K => a ᵥ* M) :=
  Matrix.vecMul_injective_iff.mpr (LagrangianRowPrefixes.rows_linearIndependent K M hM)

include c

/-- A genuine original incidence-fibre lift forces every original row
combination to lie in the ACTUAL primitive evaluation kernel. Neither
a canonical coefficient relation nor a kernel identification is supplied
as a premise. -/
theorem primitiveEvaluation_zero_of_fibre_lift (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec)
    (q : X ⟶ LagrangianFibreFactorization.fibre K
      (LagrangianMatrixPointRows.matrixPoint K M hM))
    (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
      (LagrangianMatrixPointRows.matrixPoint K M hM) = d.map) (a : Fin 5 → K) :
    primitiveEvaluation K f E b ((formsCoordinates K).symm (a ᵥ* M)) = 0 := by
  have hr := (LagrangianIncidencePlaneIso.originalFibre_factorsThrough_iff_rows
    K M hM d.map).mp ⟨q,hq⟩
  have hrows (j : Fin 5) : coordinateCanonicalEvaluation K f E b c (M j) = 0 := by
    apply (coordinateEvaluation_zero_iff_pullback K f E b c d (M j)).mpr
    simpa only [← LagrangianHyperplaneRows.determinantSection_row] using hr j
  apply primitiveEvaluation_zero_of_relation K f E b c (a ᵥ* M)
  rw [Matrix.vecMul_eq_sum, map_sum]
  simp only [map_smul, hrows, smul_zero, Finset.sum_const_zero]

end M9Native.MukaiCanonicalCoefficientRelations

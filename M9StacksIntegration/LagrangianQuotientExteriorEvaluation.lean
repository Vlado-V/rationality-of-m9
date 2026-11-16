module

public import M9StacksIntegration.LagrangianKernelPrimitiveSections
public import M9StacksIntegration.LagrangianIsotropicRestriction
public import M9StacksIntegration.LagrangianSymplecticAction

/-!
# Exterior evaluation of the original quotient sections

This uses the original six sections of an actual sheaf quotient, without
assuming that they form a basis of all H0. The standard bivector relation
is derived from the literal native sheaf relation. The native primitive
factor has exactly the original fourteen determinant-section values.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianQuotientExteriorEvaluation

open LagrangianField LagrangianGrassmannian LagrangianMatrixChart
open LagrangianKernelPrimitiveSections

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
  {Q : X.Modules} (q : freeOn X 6 ⟶ Q)

/-- The original six quotient sections in actual native cohomology. -/
def originalSection (i : Fin 6) : cohomologyOverField k f Q 0 :=
  (cohomologyOverFieldZeroLinearIso k f Q).inv
    (q.app ⊤ (freeBasisSection X 6 i))

def originalSectionMap : (Fin 6 → k) →ₗ[k] cohomologyOverField k f Q 0 :=
  ∑ i : Fin 6, (LinearMap.proj i).smulRight (originalSection k f q i)

theorem originalSectionMap_basis (i : Fin 6) :
    originalSectionMap k f q (basisVector k i) = originalSection k f q i := by
  classical
  simp [originalSectionMap, basisVector, Pi.single_apply]

theorem originalSection_sections (i : Fin 6) :
    (cohomologyOverFieldZeroLinearIso k f Q).hom (originalSection k f q i) =
      q.app ⊤ (freeBasisSection X 6 i) :=
  Iso.inv_hom_id_apply _ _

/-- The genuine exterior evaluation induced by the original six-space. -/
def lambda (n : ℕ) : (⋀[k]^n (Fin 6 → k)) →ₗ[k]
    cohomologyOverField k f (Scheme.Modules.exteriorPower Q (n : ℤ)) 0 :=
  (ExteriorEvaluation.lambda k f Q n).comp
    (exteriorPower.map n (originalSectionMap k f q))

theorem lambda_ιMulti (n : ℕ) (v : Fin n → (Fin 6 → k)) :
    lambda k f q n (exteriorPower.ιMulti k n v) =
      ExteriorEvaluation.lambda k f Q n
        (exteriorPower.ιMulti k n (fun a => originalSectionMap k f q (v a))) := by
  simp only [lambda, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti, Function.comp_def]

/-- Original native minors agree with the actual original exterior evaluation. -/
theorem lambda_thirdBasis_eq_minorH0 (i : Fin 20) :
    lambda k f q 3 (thirdBasis20 k i) = minorH0 k f q i := by
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom).injective
  rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply,
    lambda_ιMulti]
  refine (ExteriorEvaluation.lambda_ιMulti k f Q 3
    (fun a => originalSectionMap k f q (LagrangianRing.basisVector k (LagrangianRing.triple i a)))).trans ?_
  rw [minorH0, Iso.inv_hom_id_apply, LagrangianDeterminantSections.minorSection_eq_wedge]
  have hv : (fun a : Fin 3 => ExteriorEvaluation.h0SectionsSemilinear k f Q
      (originalSectionMap k f q (LagrangianRing.basisVector k (LagrangianRing.triple i a)))) =
      (fun a => q.app ⊤ (freeBasisSection X 6 (LagrangianRing.triple i a))) := by
    funext a
    change (cohomologyOverFieldZeroLinearIso k f Q).hom
      (originalSectionMap k f q (basisVector k (LagrangianRing.triple i a))) = _
    rw [originalSectionMap_basis]
    exact originalSection_sections k f q _
  rw [hv]

/-- The actual original sheaf bivector image is precisely its H0 exterior evaluation. -/
theorem lambda_two_sigma_sections :
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 2)).hom
      (lambda k f q 2 (sigma k)) =
      (exteriorPowerMap X q 2).app ⊤ (sigmaSection X) := by
  simp only [sigma, map_sum]
  rw [sigmaSection, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [lambda_ιMulti]
  refine (ExteriorEvaluation.lambda_ιMulti k f Q 2
    (fun a => originalSectionMap k f q (![e k i, LagrangianField.f k i] a))).trans ?_
  rw [exteriorPowerMap_wedgeSection, LagrangianSigmaInvariance.wedgeSection_eq_comparison]
  have hv : (fun a : Fin 2 => ExteriorEvaluation.h0SectionsSemilinear k f Q
      (originalSectionMap k f q (![e k i, LagrangianField.f k i] a))) =
      ![q.app ⊤ (freeVector X (i.castAdd 3)), q.app ⊤ (freeVector X (Fin.natAdd 3 i))] := by
    funext a
    fin_cases a
    all_goals
      change (cohomologyOverFieldZeroLinearIso k f Q).hom
        (originalSectionMap k f q (basisVector k _)) = _
      rw [originalSectionMap_basis]
      exact originalSection_sections k f q _
  rw [hv]

theorem lambda_two_sigma_eq_zero (hq : AnnihilatesSigma X q) :
    lambda k f q 2 (sigma k) = 0 := by
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 2)).hom).injective
  rw [map_zero, lambda_two_sigma_sections]
  exact hq

/-- The genuine bivector relation kills its actual degree-three products. -/
theorem lambda_three_wedgeSigma_eq_zero (hq : AnnihilatesSigma X q) (v : Fin 6 → k) :
    lambda k f q 3 (MukaiPrimitiveDuality.wedgeSigma k v) = 0 := by
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom).injective
  rw [map_zero, MukaiPrimitiveDuality.wedgeSigma_apply, map_sum, map_sum]
  have hpair (i : Fin 3) : (fun a : Fin 2 => originalSectionMap k f q
      (![e k i, LagrangianField.f k i] a)) =
      ![originalSectionMap k f q (e k i), originalSectionMap k f q (LagrangianField.f k i)] := by
    funext a
    fin_cases a <;> rfl
  have h : ∑ i : Fin 3,
      (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 2)).hom
        (ExteriorEvaluation.lambda k f Q 2 (exteriorPower.ιMulti k 2
          ![originalSectionMap k f q (e k i), originalSectionMap k f q (LagrangianField.f k i)])) = 0 := by
    simpa only [sigma, map_sum, lambda_ιMulti, hpair, map_zero] using congrArg
      (fun z => (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 2)).hom z)
      (lambda_two_sigma_eq_zero k f q hq)
  calc
    _ = ∑ i : Fin 3, ((Scheme.Modules.exteriorAlgebra Q).mul 2 1).app (op ⊤)
        ((cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 2)).hom
          (ExteriorEvaluation.lambda k f Q 2 (exteriorPower.ιMulti k 2
            ![originalSectionMap k f q (e k i), originalSectionMap k f q (LagrangianField.f k i)])))
        ((Scheme.Modules.exteriorGenerator Q).val.app (op ⊤)
          (ExteriorEvaluation.h0SectionsSemilinear k f Q (originalSectionMap k f q v))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [wedge3, lambda_ιMulti]
      have hv : (fun a : Fin 3 => originalSectionMap k f q
          (![e k i, LagrangianField.f k i, v] a)) =
          ![originalSectionMap k f q (e k i), originalSectionMap k f q (LagrangianField.f k i),
            originalSectionMap k f q v] := by
        funext a
        fin_cases a <;> rfl
      rw [hv]
      exact MukaiPrimitiveCanonicalEvaluation.lambdaThree_global_product k f Q _ _ _
    _ = _ := by
      let mv := (((Scheme.Modules.exteriorAlgebra Q).mul 2 1).app (op ⊤)).flip
        ((Scheme.Modules.exteriorGenerator Q).val.app (op ⊤)
          (ExteriorEvaluation.h0SectionsSemilinear k f Q (originalSectionMap k f q v)))
      change (∑ i : Fin 3, mv
        ((cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 2)).hom
          (ExteriorEvaluation.lambda k f Q 2 (exteriorPower.ιMulti k 2
            ![originalSectionMap k f q (e k i), originalSectionMap k f q (LagrangianField.f k i)])))) = 0
      rw [← map_sum, h, map_zero]

variable [CharZero k]

/-- The actual native primitive quotient factor, without complete-H0 assumptions. -/
def primitiveEvaluation : Module.Dual k (Primitive k) →ₗ[k]
    cohomologyOverField k f (Scheme.Modules.exteriorPower Q 3) 0 :=
  MukaiPrimitiveDuality.factor k (lambda k f q 3)

theorem primitiveEvaluation_basis (j : Fin 14) :
    primitiveEvaluation k f q ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j) =
      primitiveH0 k f q j := by
  rw [primitiveEvaluation, MukaiPrimitiveDuality.factor_basis,
    primitiveH0_eq_projectedValues]
  unfold projectedValues
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => projectionMatrix k j i • z) (lambda_thirdBasis_eq_minorH0 k f q i)

theorem range_primitiveEvaluation (hq : AnnihilatesSigma X q) :
    LinearMap.range (primitiveEvaluation k f q) = LinearMap.range (lambda k f q 3) := by
  apply Submodule.ext
  intro t
  constructor
  · rintro ⟨ell, rfl⟩
    exact ⟨(MukaiPrimitiveDuality.coefficientDuality k).symm
      (MukaiPrimitiveDuality.extension k ell), rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨MukaiPrimitiveDuality.restriction k (MukaiPrimitiveDuality.coefficientDuality k w), ?_⟩
    exact (MukaiPrimitiveDuality.factor_restriction k (lambda k f q 3)
      (lambda_three_wedgeSigma_eq_zero k f q hq)
      (MukaiPrimitiveDuality.coefficientDuality k w)).trans
        (congrArg (lambda k f q 3) ((MukaiPrimitiveDuality.coefficientDuality k).symm_apply_apply w))

theorem range_primitiveEvaluation_eq_span :
    LinearMap.range (primitiveEvaluation k f q) =
      Submodule.span k (Set.range (primitiveH0 k f q)) := by
  have hh : (primitiveEvaluation k f q) ∘
      (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis = primitiveH0 k f q := by
    funext j
    exact primitiveEvaluation_basis k f q j
  rw [LinearMap.range_eq_map,
    ← (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis.span_eq, Submodule.map_span,
    ← Set.range_comp, hh]

/-- An actual standard common-kernel relation bounds the full exterior
evaluation image, using actual isotropy rather than a rank premise. -/
theorem finrank_range_lambda_le_five (hq : AnnihilatesSigma X q)
    (hzero : q.app ⊤ (freeBasisSection X 6 0) = 0) :
    finrank k (LinearMap.range (lambda k f q 3)) ≤ 5 := by
  rw [← range_primitiveEvaluation k f q hq, range_primitiveEvaluation_eq_span]
  exact finrank_span_primitiveH0_le_five k f q hzero

end M9Native.LagrangianQuotientExteriorEvaluation

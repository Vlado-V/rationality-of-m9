module

public import M9StacksIntegration.LagrangianUniversalTriples
public import M9StacksIntegration.PrimitiveDeterminantCoefficients
public import M9StacksIntegration.LagrangianQuotientExteriorEvaluation
public import M9StacksIntegration.LagrangianPrimitiveRestriction
public import M9StacksIntegration.LagrangianPrimitiveSectionsPullback

/-!
# The original triple determinant is the original primitive hyperplane

The original six-section exterior value is identified with restriction
of the actual fourteen primitive determinant sections, using their
original coefficients. The genuine universal quotient supplies sigma
annihilation. Neither a complete-H0 basis nor a restriction-kernel
statement is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2300000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianTripleDeterminantSection

open LagrangianUniversalSections LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianKernelPrimitiveSections LagrangianQuotientExteriorEvaluation

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) (l : X ⟶ LagrangianGrassmannian.space k)

/-- The two original native cohomology functor spellings have the same morphism. -/
theorem cohomologyIso_hom_eq_map {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    (cohomologyOverFieldIso k f e n).hom = cohomologyOverFieldMap k f e.hom n := by
  with_unfolding_all rfl

/-- The literal original six-section map agrees with the arbitrary-quotient construction. -/
theorem originalSectionMap_eq :
    originalSectionMap k f (quotientMap k l) = sectionMap k f l := rfl

/-- Actual isotropy of the universal LG quotient, pulled back along the actual morphism. -/
theorem quotient_annihilates :
    LagrangianGrassmannian.AnnihilatesSigma X (quotientMap k l) :=
  LagrangianIsotropicRestriction.pulledQuotient_annihilates l
    (quotientOnLG k).map (LagrangianSymplecticAction.lagrangianUniversal_annihilates k)

/-- The native determinant-line base-change isomorphism for the original quotient. -/
def determinantIso : LagrangianPrimitiveRestriction.restrictedLine k l ≅
    Scheme.Modules.exteriorPower (bundle k l) 3 :=
  LagrangianPullback.exteriorPullbackIso l (quotientOnLG k).target 3

/-- Original primitive restriction H0 agrees with the original primitive section of q. -/
theorem primitiveRestriction_basis_transport
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (j : Fin 14) :
    (cohomologyOverFieldIso k f (determinantIso k l) 0).hom
      (LagrangianPrimitiveRestriction.sectionH0 k f l j) =
      primitiveH0 k f (quotientMap k l) j := by
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f
      (Scheme.Modules.exteriorPower (bundle k l) 3)).hom).injective
  rw [cohomologyIso_hom_eq_map]
  refine (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f
    (determinantIso k l).hom
    (LagrangianPrimitiveRestriction.sectionH0 k f l j)).trans ?_
  rw [LagrangianPrimitiveRestriction.sectionH0, Iso.inv_hom_id_apply,
    primitiveH0, Iso.inv_hom_id_apply]
  change (determinantIso k l).hom.app ⊤
    (pullbackGlobalSections l (determinantLine k) (primitiveSections k j)) = _
  exact (LagrangianPrimitiveSectionsPullback.primitiveSections_pullback k l j).trans
    (congrArg (fun c => primitiveSection X k c (quotientMap k l) j)
      (LagrangianUniversalSections.coefficients k f l hl))

/-- The actual exterior determinant evaluated on a literal original triple. -/
def determinantValue (s : Fin 3 → (Fin 6 → k)) :
    cohomologyOverField k f (Scheme.Modules.exteriorPower (bundle k l) 3) 0 :=
  ExteriorEvaluation.lambda k f (bundle k l) 3
    (exteriorPower.ιMulti k 3 (fun i => sectionMap k f l (s i)))

/-- Literal original primitive coefficients evaluate to the literal original determinant. -/
theorem determinantValue_eq_primitive_sum (s : Fin 3 → (Fin 6 → k)) :
    determinantValue k f l s =
      ∑ j : Fin 14, PrimitiveDecomposableNonzero.coefficients k s j •
        primitiveH0 k f (quotientMap k l) j := by
  have hd := LagrangianQuotientExteriorEvaluation.lambda_ιMulti k f (quotientMap k l) 3 s
  rw [originalSectionMap_eq k f l] at hd
  change LagrangianQuotientExteriorEvaluation.lambda k f (quotientMap k l) 3
    (exteriorPower.ιMulti k 3 s) = determinantValue k f l s at hd
  rw [← hd]
  refine (PrimitiveDeterminantCoefficients.evaluation_ιMulti_eq_sum k
    (LagrangianQuotientExteriorEvaluation.lambda k f (quotientMap k l) 3)
    (lambda_three_wedgeSigma_eq_zero k f (quotientMap k l)
      (quotient_annihilates k l)) s).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => PrimitiveDecomposableNonzero.coefficients k s j • z)
    (primitiveEvaluation_basis k f (quotientMap k l) j)

/-- The determinant of every original triple is exactly the actual restricted original hyperplane. -/
theorem determinantValue_eq_restriction
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (s : Fin 3 → (Fin 6 → k)) :
    determinantValue k f l s =
      (cohomologyOverFieldIso k f (determinantIso k l) 0).hom
        (LagrangianPrimitiveRestriction.primitiveRestriction k f l
          (PrimitiveDecomposableNonzero.coefficients k s)) := by
  rw [determinantValue_eq_primitive_sum,
    LagrangianPrimitiveRestriction.primitiveRestriction_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, primitiveRestriction_basis_transport k f l hl]

/-- The precise kernel test uses the original primitive restriction, with no assumed kernel size. -/
theorem determinantValue_eq_zero_iff
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (s : Fin 3 → (Fin 6 → k)) :
    determinantValue k f l s = 0 ↔
      LagrangianPrimitiveRestriction.primitiveRestriction k f l
        (PrimitiveDecomposableNonzero.coefficients k s) = 0 := by
  rw [determinantValue_eq_restriction k f l hl]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldIso k f (determinantIso k l) 0).hom).injective

/-- Thus the vanishing determinant is exactly vanishing of the actual original ambient hyperplane. -/
theorem determinantValue_eq_zero_iff_hyperplane
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (s : Fin 3 → (Fin 6 → k)) :
    determinantValue k f l s = 0 ↔
      pullbackGlobalSections l (determinantLine k)
        (LagrangianHyperplaneCoordinates.determinantSection k
          (PrimitiveDecomposableNonzero.coefficients k s)) = 0 :=
  (determinantValue_eq_zero_iff k f l hl s).trans
    (LagrangianPrimitiveRestriction.primitiveRestriction_ker_iff k f l hl _)

end M9Native.LagrangianTripleDeterminantSection

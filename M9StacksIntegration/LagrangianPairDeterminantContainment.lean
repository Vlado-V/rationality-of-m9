module

public import M9StacksIntegration.LagrangianArbitraryPairPullback
public import M9StacksIntegration.ExteriorPairZeroTriple
public import M9StacksIntegration.LagrangianTripleDeterminantSection
public import M9StacksIntegration.SectionZeroSubbundle

/-!
# The full original pair rank-drop scheme lies in the triple hyperplane

Every scheme test is retained. A pair wedge vanishes in the actual
pulled-back Q exterior sheaf; multiplication in actual local-ring
exterior algebras makes the triple wedge vanish. The frozen exact
primitive-coefficient formula identifies this with the original LG
hyperplane. No reducedness or field-point-only replacement is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
universe u

namespace M9Native.LagrangianPairDeterminantContainment
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianUniversalSections
variable (K : Type u) [Field K] [CharZero K]

/-- On ANY test, vanishing of the selected original pair wedge forces
vanishing of the original primitive determinant hyperplane. -/
theorem hyperplane_zero_of_pair_zero {X : Scheme.{u}} (l : X ⟶ space K)
    (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (he : pullbackGlobalSections l (LagrangianArbitraryPlaneIncidence.wedgeBundle K)
      (LagrangianArbitraryPlaneIncidence.wedgeEquation K (s ∘ e)) = 0) :
    pullbackGlobalSections l (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K
        (PrimitiveDecomposableNonzero.coefficients K s)) = 0 := by
  apply (LagrangianTripleDeterminantSection.determinantValue_eq_zero_iff_hyperplane K
    (l ≫ projection K) l rfl s).mp
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso K (l ≫ projection K)
      (Scheme.Modules.exteriorPower (bundle K l) (3 : ℤ))).hom).injective
  rw [map_zero]
  change (cohomologyOverFieldZeroLinearIso K (l ≫ projection K)
      (Scheme.Modules.exteriorPower (bundle K l) (3 : ℤ))).hom
    (ExteriorEvaluation.lambda K (l ≫ projection K) (bundle K l) 3
      (exteriorPower.ιMulti K 3 (fun i => sectionMap K (l ≫ projection K) l (s i)))) = 0
  refine (ExteriorEvaluation.lambda_ιMulti K (l ≫ projection K) (bundle K l) 3 _).trans ?_
  apply ExteriorPairZeroTriple.sections (bundle K l)
    (fun i => ExteriorEvaluation.h0SectionsSemilinear K (l ≫ projection K) (bundle K l)
      (sectionMap K (l ≫ projection K) l (s i))) e
  have h := congrArg
    ((LagrangianPullback.exteriorPullbackIso l (quotientOnLG K).target 2).hom.app ⊤) he
  rw [map_zero, LagrangianArbitraryPairPullback.wedgeEquation_pullback] at h
  exact (ExteriorEvaluation.lambda_ιMulti K (l ≫ projection K) (bundle K l) 2 _).symm.trans h

/-- Full closed-subscheme containment in the original determinant
hyperplane, expressed as the actual inequality of full ideal sheaves. -/
theorem hyperplaneIdeal_le_rankDrop (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :
    Stacks.Divisors.zeroScheme (space K) (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K
        (PrimitiveDecomposableNonzero.coefficients K s)) ≤
      LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) := by
  let I := LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e)
  have h := hyperplane_zero_of_pair_zero K I.subschemeι s e
    (SectionZeroIdealFactorization.pullbackGlobalSections_subschemeι_eq_zero
      (LagrangianArbitraryPlaneIncidence.wedgeBundle K) 3
      (LagrangianArbitraryPlaneIncidence.wedgeEquation K (s ∘ e)))
  have hf := (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme
    (space K) (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K
        (PrimitiveDecomposableNonzero.coefficients K s)) I.subschemeι).mp h
  have hle := (factorsThrough_ideal_iff_ideal_le_ker _ I.subschemeι).mp hf
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using hle

end M9Native.LagrangianPairDeterminantContainment

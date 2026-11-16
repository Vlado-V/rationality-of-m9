module

public import M9StacksIntegration.LagrangianPrimitiveSectionCovariance
public import M9StacksIntegration.LagrangianHyperplaneCoordinates

/-!
# Genuine coefficient covariance of every original determinant section

The positive raw primitive matrix is used with the genuine transpose LG
action fixed by the original quotient convention. All coefficient vectors
and every native test scheme are retained. These identities do not assume
an action comparison, a frame, or a geometric fibre isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
open scoped BigOperators
universe u

namespace M9Native.LagrangianSectionCoefficientCovariance

open LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianSigmaInvariance

variable (K : Type u) [Field K] [CharZero K]

/-- The literal positive raw primitive coefficient matrix. -/
abbrev coefficientMatrix (g : Matrix.symplecticGroup (Fin 3) K) : Matrix (Fin 14) (Fin 14) K :=
  PrimitiveRingMatrices.matrix14 K K (RingHom.id K) g

/-- Pullback of a row coefficient vector uses the actual positive raw matrix. -/
def coefficientRow (g : Matrix.symplecticGroup (Fin 3) K) (v : Fin 14 → K) : Fin 14 → K :=
  v ᵥ* coefficientMatrix K g

/-- The original structural coefficient map is retained on all native tests. -/
theorem determinantSection_pullback {T : Scheme.{u}} (f : T ⟶ space K) (v : Fin 14 → K) :
    pullbackGlobalSections f (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K v) =
        ∑ j : Fin 14, LagrangianPlucker.coefficientMap K f (v j) •
          pullbackGlobalSections f (determinantLine K) (primitiveSections K j) := by
  have hc (a : K) : f.appTop (LagrangianHyperplaneCoordinates.coefficientMap K a) =
      LagrangianPlucker.coefficientMap K f a := by
    change f.appTop.hom (LagrangianHyperplaneCoordinates.coefficientMap K a) = _
    have h := RingHom.congr_fun
      (LagrangianPlucker.coefficientMap_comp K (𝟙 (space K)) f) a
    simpa only [Category.comp_id, RingHom.comp_apply,
      LagrangianHyperplaneCoordinates.coefficientMap] using h.symm
  simp only [LagrangianHyperplaneCoordinates.determinantSection, map_sum,
    SectionsEqualizer.pullbackGlobalSections_smul, hc]

private theorem exchange_coefficients {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (κ : K →+* R) (A : Matrix (Fin 14) (Fin 14) K) (v : Fin 14 → K) (s : Fin 14 → W) :
    (∑ j : Fin 14, κ (v j) • ∑ a : Fin 14, κ (A j a) • s a) =
      ∑ a : Fin 14, κ ((v ᵥ* A) a) • s a := by
  simp only [Finset.smul_sum, smul_smul, Matrix.vecMul_apply_eq_sum, map_sum,
    map_mul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Actual determinant-line covariance for every original coefficient
vector, with the proved original transpose convention. -/
theorem determinantActionIso_coefficients {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) (v : Fin 14 → K) :
    (LagrangianDeterminantAction.determinantActionIso K f (transposeSymplectic K g)).hom.app ⊤
      (pullbackGlobalSections (f ≫ LagrangianSymplecticAction.action K (transposeSymplectic K g))
        (determinantLine K) (LagrangianHyperplaneCoordinates.determinantSection K v)) =
      pullbackGlobalSections f (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (coefficientRow K g v)) := by
  rw [determinantSection_pullback, determinantSection_pullback]
  simp only [map_sum, Scheme.Modules.Hom.app_smul,
    LagrangianDeterminantAction.coefficientMap_action]
  simp_rw [LagrangianPrimitiveSectionCovariance.determinantActionIso_transpose_primitive_covariance]
  exact exchange_coefficients K (LagrangianPlucker.coefficientMap K f)
    (coefficientMatrix K g) v (fun a =>
      pullbackGlobalSections f (determinantLine K) (primitiveSections K a))

/-- The true equation vanishing equivalence on every native test scheme. -/
theorem pullback_action_zero_iff {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) (v : Fin 14 → K) :
    pullbackGlobalSections (f ≫ LagrangianSymplecticAction.action K (transposeSymplectic K g))
        (determinantLine K) (LagrangianHyperplaneCoordinates.determinantSection K v) = 0 ↔
      pullbackGlobalSections f (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (coefficientRow K g v)) = 0 := by
  rw [← determinantActionIso_coefficients K f g v]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((LagrangianDeterminantAction.determinantActionIso K f
      (transposeSymplectic K g)).hom.app ⊤)).injective).symm

end M9Native.LagrangianSectionCoefficientCovariance

module

public import M9StacksIntegration.MukaiEulerProjection
public import M9StacksIntegration.MukaiConormalLinearJets

/-! The original native conormal Euler coefficients are a single derived
nonzero scalar times the genuine ratio-basis elementary vectors. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace M9Native.MukaiConormalCoefficientImage

open LagrangianGrassmannian LagrangianPlucker LagrangianPluckerQuotient
open MukaiConormalOriginCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] [CharZero K]
variable (p : Spec (.of K) ⟶ space K)
variable (τ : (Scheme.Modules.pullback p).obj (determinantLine K) ≅
  SheafOfModules.unit (Spec (.of K)).ringCatSheaf)
variable (i : Fin 14)
variable (hp : ProjectiveEulerFieldPoint.image (ULift.{u} ℤ) 13 K
    (p ≫ integralPrimitivePlucker K) ∈
  ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) 13) (MvPolynomial.X i))

def pairedCoefficients : MukaiEulerFieldPoint.Source K p →ₗ[K] (Fin 14 → K) :=
  LinearMap.pi (fun k => MukaiEulerFieldPoint.coefficient K p k)

theorem sourceCoordinates_basis (j : {j : Fin 14 // j ≠ i}) :
    MukaiEulerFieldPoint.sourceCoordinates K p τ (MukaiEulerFieldPoint.basis K p τ i hp j) =
      ProjectiveEulerFieldPoint.cotangentBasis (ULift.{u} ℤ) 13 K
        (p ≫ integralPrimitivePlucker K) i hp j := by
  change (MukaiEulerFieldPoint.sourceCoordinates K p τ)
    ((MukaiEulerFieldPoint.sourceCoordinates K p τ).symm
      (ProjectiveEulerFieldPoint.cotangentBasis (ULift.{u} ℤ) 13 K
        (p ≫ integralPrimitivePlucker K) i hp j)) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The scalar is derived from the actual native line pairing and actual
frame, and is uniform for every input and original coordinate. -/
theorem pairedCoefficients_factor :
    ∃ a : K, a ≠ 0 ∧ pairedCoefficients K p = a •
      MukaiConormalLinearJets.eulerMap K
        (ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) 13 K
          (p ≫ integralPrimitivePlucker K) i hp) i (MukaiEulerFieldPoint.basis K p τ i hp) := by
  obtain ⟨a,ha,h⟩ := MukaiEulerFieldPoint.exists_uniform_scalar K p τ i hp
  refine ⟨a,ha,?_⟩
  apply (MukaiEulerFieldPoint.basis K p τ i hp).ext
  intro j
  ext k
  simpa only [pairedCoefficients, LinearMap.pi_apply, LinearMap.smul_apply,
    RingHom.id_apply, Pi.smul_apply, smul_eq_mul, MukaiConormalLinearJets.eulerMap_basis] using h j k

variable [IsAlgClosed K]

/-- This is the original frozen actual coefficientMap, on its original
conormal source. Its factorization is derived from projection coherence. -/
theorem coefficientMap_factor :
    ∃ a : K, a ≠ 0 ∧ MukaiConormalFieldCoordinates.coefficientMap K p = a •
      (MukaiConormalLinearJets.eulerMap K
        (ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) 13 K
          (p ≫ integralPrimitivePlucker K) i hp) i
        (MukaiEulerFieldPoint.basis K p τ i hp)).comp (MukaiEulerFieldPoint.conormalInput K p) := by
  obtain ⟨a,ha,h⟩ := pairedCoefficients_factor K p τ i hp
  refine ⟨a,ha,?_⟩
  ext y k
  rw [MukaiEulerProjection.coefficientMap_eq]
  have hc := congrArg (fun f : MukaiEulerFieldPoint.Source K p →ₗ[K] (Fin 14 → K) =>
    f (MukaiEulerFieldPoint.conormalInput K p y) k) h
  simpa only [pairedCoefficients, LinearMap.pi_apply, LinearMap.smul_apply,
    RingHom.id_apply, Pi.smul_apply, smul_eq_mul, LinearMap.comp_apply] using hc

/-- The literal primitive-form image retains the same actual cotangent
input and the same derived common nonzero scalar. -/
theorem formsMap_factor :
    ∃ a : K, a ≠ 0 ∧ ∀ y : MukaiConormalFieldCoordinates.Source K p,
      MukaiConormalFieldCoordinates.formsMap K p y =
        a • (formsCoordinates K).symm
          (MukaiConormalLinearJets.eulerMap K
            (ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) 13 K
              (p ≫ integralPrimitivePlucker K) i hp) i
            (MukaiEulerFieldPoint.basis K p τ i hp) (MukaiEulerFieldPoint.conormalInput K p y)) := by
  obtain ⟨a,ha,h⟩ := coefficientMap_factor K p τ i hp
  refine ⟨a,ha,fun y => ?_⟩
  have hc := congrArg (fun f : MukaiConormalFieldCoordinates.Source K p →ₗ[K] (Fin 14 → K) => f y) h
  change (formsCoordinates K).symm (MukaiConormalFieldCoordinates.coefficientMap K p y) = _
  rw [show MukaiConormalFieldCoordinates.coefficientMap K p y = a •
      MukaiConormalLinearJets.eulerMap K
        (ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) 13 K
          (p ≫ integralPrimitivePlucker K) i hp) i (MukaiEulerFieldPoint.basis K p τ i hp)
          (MukaiEulerFieldPoint.conormalInput K p y) from by
    simpa only [LinearMap.smul_apply, RingHom.id_apply, LinearMap.comp_apply] using hc]
  exact (formsCoordinates K).symm.map_smul _ _

end M9Native.MukaiConormalCoefficientImage

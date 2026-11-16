module

public import M9StacksIntegration.ProjectiveEulerCompositeLine
public import M9StacksIntegration.MukaiConormalDifferentialTransport

/-! Actual integral fourteen-coordinate Euler source at a native LG field
point, with the original determinant pairing and the actual differential. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace M9Native.MukaiEulerFieldPoint

open LagrangianGrassmannian LagrangianPlucker LagrangianPluckerQuotient MukaiBundleDeterminant
open MukaiConormalEuler MukaiConormalEulerPairing MukaiConormalRank
open MukaiConormalCotangentTransport MukaiConormalDifferentialTransport

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] [CharZero K]
variable (p : Spec (.of K) ⟶ space K)
variable (τ : (Scheme.Modules.pullback p).obj (determinantLine K) ≅
  SheafOfModules.unit (Spec (.of K)).ringCatSheaf)

abbrev Source := moduleSpecΓFunctor.obj
  ((Scheme.Modules.pullback p).obj (twistedEulerSequence K).X₁)

/-- This is exactly pullback-tensor, the actual determinant frame, the
native unit, and pullback-composition on the ORIGINAL integral cotangent. -/
def sourceCoordinates : Source K p ≃ₗ[K]
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (p ≫ integralPrimitivePlucker K)).obj
      (Scheme.Hom.relativeDifferentials (integralProjection 13))) :=
  ProjectiveEulerCompositeLine.sourceCoordinates (ULift.{u} ℤ) 13 K
    (integralPrimitivePlucker K) p (determinantLine K) τ
    (Scheme.Hom.relativeDifferentials (integralProjection 13))

def cotangentInput : Source K p →ₗ[K]
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj
      ((Scheme.Modules.pullback (integralPrimitivePlucker K)).obj
        (Scheme.Hom.relativeDifferentials (integralProjection 13)))) :=
  (moduleSpecΓFunctor.map
    ((Scheme.Modules.pullbackComp p (integralPrimitivePlucker K)).app
      (Scheme.Hom.relativeDifferentials (integralProjection 13))).inv).hom.comp
        (sourceCoordinates K p τ).toLinearMap

/-- Zero of the literal pulled determinant-tensor differential gives
zero on the same original cotangent input, with no image premise. -/
theorem integralDifferential_zero_of_tensor_zero (x : Source K p)
    (hx : (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      ((determinantTensorRight K).map (integralDifferential K)))).hom x = 0) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (integralDifferential K))).hom
      (cotangentInput K p τ x) = 0 :=
  ProjectiveEulerCompositeLine.map_zero_of_tensor_map_zero (ULift.{u} ℤ) 13 K
    (integralPrimitivePlucker K) p (determinantLine K) τ
    (Scheme.Hom.relativeDifferentials (integralProjection 13)) (integralDifferential K) x hx

def conormalInput : moduleSpecΓFunctor.obj
    ((Scheme.Modules.pullback p).obj (MukaiConormalBundle.twistedConormal K)) →ₗ[K] Source K p :=
  (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
    ((determinantTensorRight K).map (conormalToIntegralCotangent K)))).hom

/-- The preceding zero hypothesis is DERIVED for the actual original
conormal input from the literal native conormal differential composition. -/
theorem integralDifferential_conormal_zero
    (y : moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback p).obj (MukaiConormalBundle.twistedConormal K))) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (integralDifferential K))).hom
      (cotangentInput K p τ (conormalInput K p y)) = 0 := by
  apply integralDifferential_zero_of_tensor_zero
  have h : (Scheme.Modules.pullback p).map
      ((determinantTensorRight K).map (conormalToIntegralCotangent K)) ≫
        (Scheme.Modules.pullback p).map
          ((determinantTensorRight K).map (integralDifferential K)) = 0 := by
    rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp,
      conormalToIntegralCotangent_comp_integralDifferential]
    simp only [CategoryTheory.Functor.map_zero]
  have hΓ := congrArg (fun t => (moduleSpecΓFunctor.map t).hom y) h
  simp only [CategoryTheory.Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply,
    CategoryTheory.Functor.map_zero,ModuleCat.hom_zero,LinearMap.zero_apply] at hΓ
  exact hΓ

/-- Coefficients of the actual integral Euler map followed by its
ORIGINAL component and the ORIGINAL negative-determinant pairing. -/
def coefficient (k : Fin 14) : Source K p →ₗ[K] K :=
  ProjectiveEulerCompositeLine.coefficient (ULift.{u} ℤ) 13 K
    (integralPrimitivePlucker K) p (determinantLine K) (negativeDeterminantPairingIso K) k

variable (i : Fin 14)
variable (hp : ProjectiveEulerFieldPoint.image (ULift.{u} ℤ) 13 K
    (p ≫ integralPrimitivePlucker K) ∈
  ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) 13) (MvPolynomial.X i))

/-- A genuine basis of the actual determinant-twisted integral source;
its vectors retain the actual pulled ratio differentials. -/
def basis : Module.Basis {j : Fin 14 // j ≠ i} K (Source K p) :=
  ProjectiveEulerCompositeLine.basis (ULift.{u} ℤ) 13 K
    (integralPrimitivePlucker K) p (determinantLine K) τ i hp

theorem exists_uniform_scalar :
    ∃ a : K, a ≠ 0 ∧ ∀ (j : {j : Fin 14 // j ≠ i}) (k : Fin 14),
      coefficient K p k (basis K p τ i hp j) =
        a * Stacks.LinearAlgebra.kernelGen
          (ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) 13 K
            (p ≫ integralPrimitivePlucker K) i hp) i j.1 k :=
  ProjectiveEulerCompositeLine.exists_uniform_scalar (ULift.{u} ℤ) 13 K
    (integralPrimitivePlucker K) p (determinantLine K) τ
      (negativeDeterminantPairingIso K) i hp

end M9Native.MukaiEulerFieldPoint

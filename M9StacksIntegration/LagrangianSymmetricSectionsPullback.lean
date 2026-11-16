module

public import M9StacksIntegration.LagrangianSymmetricPlucker
public import M9StacksIntegration.LagrangianPlaneHyperplanes

/-! Exact all-test comparison between the native quotient-plane equations
and the original determinant sections. Vanishing is transported through
the actual native pullback comparison and actual twisting-line isomorphism,
including for nonreduced test schemes. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianProjectiveLinearForms
open M9Native.LagrangianProjectivePlaneKernel M9Native.LagrangianSymmetricPlucker
open AlgebraicGeometry.ProjectiveSpaceOfModule AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

universe u

namespace M9Native.LagrangianSymmetricSectionsPullback

variable (K : Type u) [Field K] [CharZero K]
attribute [local instance] LagrangianSymmetricPlucker.overBase globalSectionsModule

theorem pullback_section_zero_iff {T : Scheme.{u}} (t : T ⟶ space K) (v : Forms K) :
    pullbackGlobalSections (t ≫ canonicalPlucker K)
      (twistingSheafModule (sourceGrading K) (1 : ℤ))
      (degreeSection (sourceGrading K) 1
        ⟨SymmetricAlgebra.ι K (Forms K) v,
          AlgebraicGeometry.ProjectiveSpaceOfModule.ι_mem_symmetricPower_one K (Forms K) v⟩) = 0 ↔
    pullbackGlobalSections t (determinantLine K) (sectionLinear K v) = 0 := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  have hc := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp t (canonicalPlucker K)).hom.app
      (twistingSheafModule (sourceGrading K) (1 : ℤ))).app ⊤)).injective
  rw [map_eq_zero_iff _ hc]
  have h := LagrangianMatrixChart.pullbackSection_eq_zero_iff_of_iso t
    (symmetricDeterminantIso K)
    (pullbackGlobalSections (canonicalPlucker K)
      (twistingSheafModule (sourceGrading K) (1 : ℤ))
      (degreeSection (sourceGrading K) 1
        ⟨SymmetricAlgebra.ι K (Forms K) v,
          AlgebraicGeometry.ProjectiveSpaceOfModule.ι_mem_symmetricPower_one K (Forms K) v⟩))
  rw [symmetricDeterminantIso_section] at h
  exact h

/-- Exact original-map factorization through the actual closed quotient
plane is vanishing of the original five determinant-section combinations. -/
theorem originalPlucker_factorsThrough_iff {T : Scheme.{u}} (t : T ⟶ space K)
    (L : Coordinates K →ₗ[K] (Fin 5 → K)) :
    (∃ g : T ⟶ projectiveSpaceOfModule K (Forms K ⧸ constraints K L),
      g ≫ quotientMap K (Forms K) (constraints K L) =
        t ≫ LagrangianPlucker.primitivePlucker K ≫ (coordinateIso K).hom) ↔
    ∀ j : Fin 5, pullbackGlobalSections t (determinantLine K)
      (sectionLinear K (rowForms K L j)) = 0 := by
  rw [← canonicalPlucker_eq]
  rw [LagrangianPlaneHyperplanes.factorsThrough_iff_sections_zero]
  apply forall_congr'
  intro j
  exact pullback_section_zero_iff K t (rowForms K L j)

end M9Native.LagrangianSymmetricSectionsPullback

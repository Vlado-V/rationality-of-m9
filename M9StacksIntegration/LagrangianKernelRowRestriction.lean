module

public import M9StacksIntegration.LagrangianKernelSymmetricSections
public import M9StacksIntegration.LagrangianHyperplaneRows
public import M9StacksIntegration.IteratedLineSectionCuts

/-!
# The actual original fourteen equations restricted to the five-space

Every original coefficient vector is restricted by the proved literal
primitive expansion. The actual structural scalar maps are retained, so
simultaneous vanishing is compared on arbitrary native test schemes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators
universe u

namespace M9Native.LagrangianKernelRowRestriction

open LagrangianCommonKernelZero LagrangianPluckerQuotient LagrangianKernelFivePullback
open LagrangianKernelSymmetricSections LagrangianCommonKernelSpan
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections

attribute [local instance] LagrangianKernelSymmetricSections.overBase globalSectionsModule

variable (K : Type u) [Field K] [CharZero K]

def coefficientRestriction (v : Fin 14 → K) : coefficientSpace K :=
  fun a => ∑ j : Fin 14, v j * embeddingFourteen K (Pi.single a 1) j

def rows (M : Matrix (Fin 5) (Fin 14) K) : Fin 5 → coefficientSpace K :=
  fun j => coefficientRestriction K (M j)

/-- Actual pullback of the original structural coefficients. -/
theorem coefficientMap_pullback :
    (zeroInclusion K).appTop.hom.comp (LagrangianHyperplaneCoordinates.coefficientMap K) =
      Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom K (zeroSpace K) := by
  change (zeroInclusion K).appTop.hom.comp (LagrangianPlucker.coefficientMap K (𝟙 _)) =
    LagrangianPlucker.coefficientMap K (zeroInclusion K)
  simpa only [Category.comp_id] using
    (LagrangianPlucker.coefficientMap_comp K (𝟙 _) (zeroInclusion K)).symm

/-- The original native row section restricts to its genuine five-space linear form. -/
theorem determinantSection_pullback (v : Fin 14 → K) :
    pullbackGlobalSections (zeroInclusion K) (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K v) =
        sectionLinear K (coefficientRestriction K v) := by
  have hc (c : K) : (zeroInclusion K).appTop
      (LagrangianHyperplaneCoordinates.coefficientMap K c) =
      Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom K (zeroSpace K) c :=
    RingHom.congr_fun (coefficientMap_pullback K) c
  have hscalar (c : K) (w : Γ(line K, ⊤)) :
      Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom K (zeroSpace K) c • w =
        c • w := rfl
  have hp (j : Fin 14) :
      pullbackGlobalSections (zeroInclusion K) (determinantLine K) (primitiveSections K j) =
        ∑ a : Fin 5, embeddingFourteen K (Pi.single a 1) j •
          pulledFiveSections K (zeroInclusion K) a :=
    LagrangianKernelChartTriangle.pulledPrimitive_expansion K (zeroInclusion K)
      (quotient_first_section_zero K) j
  calc
    _ = ∑ j : Fin 14, v j • pullbackGlobalSections (zeroInclusion K)
        (determinantLine K) (primitiveSections K j) := by
      simp only [LagrangianHyperplaneCoordinates.determinantSection,
        map_sum, SectionsEqualizer.pullbackGlobalSections_smul, hc]
      exact Finset.sum_congr rfl (fun j _ => hscalar (v j) _)
    _ = ∑ j : Fin 14, v j • ∑ a : Fin 5,
        embeddingFourteen K (Pi.single a 1) j • pulledFiveSections K (zeroInclusion K) a := by
      simp_rw [hp]
    _ = _ := by
      rw [sectionLinear_apply]
      simp only [coefficientRestriction, Finset.sum_smul, mul_smul, Finset.smul_sum]
      exact Finset.sum_comm

/-- Every test scheme sees the same actual equations after restriction. -/
theorem pullback_row_zero_iff {T : Scheme.{u}} (t : T ⟶ zeroSpace K) (v : Fin 14 → K) :
    pullbackGlobalSections (t ≫ zeroInclusion K) (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K v) = 0 ↔
    pullbackGlobalSections t (line K) (sectionLinear K (coefficientRestriction K v)) = 0 := by
  rw [IteratedLineSectionCuts.pullback_comp_zero_iff,
    determinantSection_pullback]

end M9Native.LagrangianKernelRowRestriction

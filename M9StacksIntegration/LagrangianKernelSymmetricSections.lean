module

public import M9StacksIntegration.LagrangianCommonKernelQuadricIso
public import M9StacksIntegration.LagrangianSymmetricPlucker

/-!
# The original five sections in the native symmetric-projective model

The five actual determinant sections classify a genuine morphism to the
projective space of the original five-dimensional coefficient module.
The native twisting-line isomorphism recovers every linear combination.
Its polynomial coordinate map is the already-proved original quadric map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TopologicalSpace
open Stacks.NonvanishingOpen
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents
open Stacks.AlgebraicGeometry.ProjBaseChange
open scoped BigOperators
universe u

namespace M9Native.LagrangianKernelSymmetricSections

open LagrangianCommonKernelZero LagrangianKernelFivePullback LagrangianKernelFiveSections
open LagrangianPluckerQuotient LagrangianProjectiveSections
open LagrangianCommonKernelQuadricIso

variable (K : Type u) [Field K] [CharZero K]

abbrev coefficientSpace := Fin 5 → K
abbrev grading := fun d : ℕ => SymPow.symmetricPower d K (coefficientSpace K)
abbrev line : (zeroSpace K).Modules :=
  (Scheme.Modules.pullback (zeroInclusion K)).obj (determinantLine K)

@[instance_reducible] def overBase : (zeroSpace K).Over (Spec (.of K)) := ⟨zeroProjection K⟩
attribute [local instance] overBase globalSectionsModule

/-- The actual original five-coordinate linear system, with the true base action. -/
def sectionLinear : coefficientSpace K →ₗ[K] Γ(line K, ⊤) :=
  (Pi.basisFun K (Fin 5)).constr K (pulledFiveSections K (zeroInclusion K))

theorem sectionLinear_basis (i : Fin 5) :
    sectionLinear K ((Pi.basisFun K (Fin 5)) i) =
      pulledFiveSections K (zeroInclusion K) i := Basis.constr_basis _ _ _ i

theorem sectionLinear_apply (v : coefficientSpace K) : sectionLinear K v =
    ∑ i : Fin 5, v i • pulledFiveSections K (zeroInclusion K) i := by
  have h := congrArg (sectionLinear K) ((Pi.basisFun K (Fin 5)).sum_repr v)
  simpa only [map_sum, map_smul, sectionLinear_basis, Pi.basisFun_repr] using h.symm

theorem sectionLinear_generates :
    ⨆ v : coefficientSpace K,
      nonvanishingOpen (zeroSpace K) (line K) (sectionLinear K v) = ⊤ := by
  apply eq_top_iff.mpr
  intro x hx
  obtain ⟨i, hi⟩ := (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem _).mp
    (pulledFiveSections_generatesStalks K (zeroProjection K) (zeroInclusion K) rfl
      (quotient_first_section_zero K)) x
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨(Pi.basisFun K (Fin 5)) i, by simpa only [sectionLinear_basis] using hi⟩

/-- The genuine native morphism of these actual generating sections. -/
def symmetricMap : zeroSpace K ⟶ projectiveSpaceOfModule K (coefficientSpace K) :=
  morphismOfGeneratingSections K (coefficientSpace K) (line K)
    (sectionLinear K) (sectionLinear_generates K)

/-- Its actual twisting-line comparison, without a supplied line isomorphism. -/
def symmetricLineIso :
    (Scheme.Modules.pullback (symmetricMap K)).obj
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (grading K) (1 : ℤ)) ≅
        line K :=
  twistIsoOfGeneratingSections K (coefficientSpace K) (line K)
    (sectionLinear K) (sectionLinear_generates K)

theorem symmetricLineIso_section (v : coefficientSpace K) :
    (symmetricLineIso K).hom.app ⊤
      (pullbackGlobalSections (symmetricMap K)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (grading K) (1 : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading K) 1
          ⟨SymmetricAlgebra.ι K (coefficientSpace K) v,
            AlgebraicGeometry.ProjectiveSpaceOfModule.ι_mem_symmetricPower_one K (coefficientSpace K) v⟩)) =
      sectionLinear K v :=
  twistIso_pullbackSectionOne K (coefficientSpace K) (line K)
    (sectionLinear K) (sectionLinear_generates K) v

/-- The actual module-projective map is the original five-section map
in the genuine native basis coordinates. -/
theorem symmetricMap_eq : symmetricMap K = zeroProjectiveMap K ≫
    (basisProjectiveSpaceIso (Pi.basisFun K (Fin 5))).hom := by
  apply (cancel_mono (basisProjectiveSpaceIso (Pi.basisFun K (Fin 5))).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso
    (Pi.basisFun K (Fin 5)) (sectionLinear K) (sectionLinear_generates K)
  have hs : basisSections (Pi.basisFun K (Fin 5)) (sectionLinear K) =
      pulledFiveSections K (zeroInclusion K) := funext (sectionLinear_basis K)
  change symmetricMap K ≫
    (basisProjectiveSpaceOfModuleIso (Pi.basisFun K (Fin 5))).hom.left = _
  have hb : (zeroSpace K ↘ Spec (.of K)) = zeroProjection K := rfl
  refine h.trans ?_
  simpa only [hs, hb, zeroProjectiveMap] using (projectiveMap_eq_pulled K
    (zeroProjection K) (zeroInclusion K) rfl (quotient_first_section_zero K)).symm

/-- The literal polynomial coordinates and the actual symmetric coordinates agree. -/
theorem symmetricMap_toPolynomial : symmetricMap K ≫
    (SplitQuadricLinearSection.coordinateIso K).hom = zeroPolynomialMap K := by
  rw [symmetricMap_eq, basisProjectiveSpaceIso_hom,
    ← modulePolynomialIso_inv (Pi.basisFun K (Fin 5))]
  simp only [SplitQuadricLinearSection.coordinateIso, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, zeroPolynomialMap]

/-- The proved global quadric model retains the actual module-projective map. -/
theorem modelIso_toSymmetric : (modelIso K).hom ≫
    SplitQuadricLinearSection.quadricInclusion K ≫
      (SplitQuadricLinearSection.coordinateIso K).inv = symmetricMap K := by
  apply (cancel_mono (SplitQuadricLinearSection.coordinateIso K).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (modelIso_hom_ambient K).trans (symmetricMap_toPolynomial K).symm

/-- Exact vanishing comparison for every native test scheme and every
actual linear combination, including nonreduced test schemes. -/
theorem pullback_section_zero_iff {T : Scheme.{u}} (t : T ⟶ zeroSpace K)
    (v : coefficientSpace K) :
    pullbackGlobalSections (t ≫ symmetricMap K)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (grading K) (1 : ℤ))
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading K) 1
        ⟨SymmetricAlgebra.ι K (coefficientSpace K) v,
          AlgebraicGeometry.ProjectiveSpaceOfModule.ι_mem_symmetricPower_one K (coefficientSpace K) v⟩) = 0 ↔
    pullbackGlobalSections t (line K) (sectionLinear K v) = 0 := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  have hc := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp t (symmetricMap K)).hom.app
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (grading K) (1 : ℤ))).app ⊤)).injective
  rw [map_eq_zero_iff _ hc]
  have h := LagrangianMatrixChart.pullbackSection_eq_zero_iff_of_iso t
    (symmetricLineIso K)
    (pullbackGlobalSections (symmetricMap K)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (grading K) (1 : ℤ))
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading K) 1
        ⟨SymmetricAlgebra.ι K (coefficientSpace K) v,
          AlgebraicGeometry.ProjectiveSpaceOfModule.ι_mem_symmetricPower_one K (coefficientSpace K) v⟩))
  rw [symmetricLineIso_section] at h
  exact h

end M9Native.LagrangianKernelSymmetricSections

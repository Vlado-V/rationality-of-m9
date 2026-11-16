module

public import M9StacksIntegration.LagrangianPluckerGeneration
public import M9StacksIntegration.LagrangianProjectivePlaneKernel
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare

/-! The original fourteen determinant sections classify the original
Plucker map in the actual symmetric-algebra projective model. Its actual
twisting-line isomorphism recovers every linear combination, with the
original structural-map scalar convention retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TopologicalSpace
open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianProjectiveLinearForms
open M9Native.LagrangianProjectivePlaneKernel
open Stacks.NonvanishingOpen
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents
open scoped BigOperators

universe u

namespace M9Native.LagrangianSymmetricPlucker

variable (K : Type u) [Field K] [CharZero K]

@[instance_reducible] def overBase : (space K).Over (Spec (.of K)) := ⟨projection K⟩
attribute [local instance] overBase globalSectionsModule

def sectionLinear : Forms K →ₗ[K] Γ(determinantLine K, ⊤) :=
  (Pi.basisFun K (Fin 14)).dualBasis.constr K (primitiveSections K)

omit [CharZero K] in
theorem sectionLinear_basis (i : Fin 14) :
    sectionLinear K ((Pi.basisFun K (Fin 14)).dualBasis i) = primitiveSections K i := by
  exact Basis.constr_basis _ _ _ i

theorem sectionLinear_generates :
    ⨆ v : Forms K, nonvanishingOpen (space K) (determinantLine K) (sectionLinear K v) = ⊤ := by
  apply eq_top_iff.mpr
  intro x hx
  obtain ⟨i, hi⟩ := (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem _).mp
    (LagrangianPluckerEpimorphism.primitiveSections_generatesStalks K) x
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨(Pi.basisFun K (Fin 14)).dualBasis i, by simpa only [sectionLinear_basis] using hi⟩

def canonicalPlucker : space K ⟶ projectiveSpaceOfModule K (Forms K) :=
  morphismOfGeneratingSections K (Forms K) (determinantLine K)
    (sectionLinear K) (sectionLinear_generates K)

/-- The native coordinate square identifies the actual canonical
symmetric-algebra map with the original fixed14 Plucker embedding. -/
theorem canonicalPlucker_eq : canonicalPlucker K =
    LagrangianPlucker.primitivePlucker K ≫ (coordinateIso K).hom := by
  apply (cancel_mono (coordinateIso K).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso
    (Pi.basisFun K (Fin 14)).dualBasis (sectionLinear K) (sectionLinear_generates K)
  have hs : basisSections (Pi.basisFun K (Fin 14)).dualBasis (sectionLinear K) =
      primitiveSections K := funext (sectionLinear_basis K)
  change canonicalPlucker K ≫
    (basisProjectiveSpaceOfModuleIso (Pi.basisFun K (Fin 14)).dualBasis).hom.left = _
  have hb : (space K ↘ Spec (.of K)) = projection K := rfl
  refine h.trans ?_
  simpa only [hs, hb] using
    (LagrangianPluckerGeneration.primitivePlucker_eq_toProjectiveSpaceOver K).symm

def symmetricDeterminantIso :
    (Scheme.Modules.pullback (canonicalPlucker K)).obj
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (sourceGrading K) (1 : ℤ)) ≅
      determinantLine K :=
  twistIsoOfGeneratingSections K (Forms K) (determinantLine K)
    (sectionLinear K) (sectionLinear_generates K)

/-- Exact recovery of the original section for every actual linear form. -/
theorem symmetricDeterminantIso_section (v : Forms K) :
    (symmetricDeterminantIso K).hom.app ⊤
      (pullbackGlobalSections (canonicalPlucker K)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (sourceGrading K) (1 : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (sourceGrading K) 1
          ⟨SymmetricAlgebra.ι K (Forms K) v,
            AlgebraicGeometry.ProjectiveSpaceOfModule.ι_mem_symmetricPower_one K (Forms K) v⟩)) =
      sectionLinear K v := by
  exact twistIso_pullbackSectionOne K (Forms K) (determinantLine K)
    (sectionLinear K) (sectionLinear_generates K) v

omit [CharZero K] in
/-- Literal fixed14 coefficients, for the actual structural-map module
convention on the original determinant sections. -/
theorem sectionLinear_matrix_row (A : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    sectionLinear K (rowForms K A.mulVecLin j) =
      ∑ i : Fin 14, A j i • primitiveSections K i := by
  rw [rowForms_matrix_expansion, map_sum]
  simp only [map_smul, sectionLinear_basis]

end M9Native.LagrangianSymmetricPlucker

module

public import M9StacksIntegration.LagrangianParameterRowComparison
public import M9StacksIntegration.SplitMatrixGrassmannianNaturality

/-! The original incidence equations at an arbitrary surjective five by
fourteen field matrix. Its actual quotient frame is derived from the
native representing class, and retains the original literal matrix. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianParameterRowComparison M9Native.LagrangianIncidenceRows
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianProjectiveLinearForms
open M9Native.LagrangianSymmetricPlucker
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open M9Native.SplitMatrixGrassmannian M9Native.SplitMatrixGrassmannianNaturality
open scoped BigOperators

universe u

namespace M9Native.LagrangianMatrixPointRows

variable (K : Type u) [Field K]

abbrev matrixPoint (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) : Spec (.of K) ⟶ parameter K :=
  fieldPoint 9 14 K M hM

theorem quotientFrame {T : Scheme.{u}} (f : T ⟶ LagrangianLinearSections.ambient K)
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
    (hf : f ≫ toParameter K =
      ((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K) ≫ matrixPoint K M hM) :
    ∃ d : (Scheme.Modules.pullback f).obj (quotientFive K) ≅ freeOn T 5,
      (pullbackPresentation f (ambientQuotient K)).map ≫ d.hom =
        Stacks.FreeSheafMatrix.ofMatrix
          (M.map (scalarMap K ((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K))) := by
  let h := (f ≫ toLG K) ≫ LagrangianGrassmannian.projection K
  let κ := (Scheme.ΓSpecIso (.of K)).inv.hom
  let N := fieldRightInverse 9 14 K M hM
  have hMN : M.map κ * N.map κ = 1 := fieldRightInverse_map_spec 9 14 K κ M hM
  have hp : pointClass 9 14 K (matrixPoint K M hM) =
      ⟦presentation (Spec (.of K)) 9 14 (M.map κ) (N.map κ) hMN⟧ :=
    fieldPoint_class 9 14 K M hM
  have hc := LagrangianLinearSectionQuotientCharts.pullback_parameter_class K (f ≫ toParameter K)
  rw [hf] at hc
  have hc' := class_comp_of_matrix_class h 9 14 K (matrixPoint K M hM)
    (M.map κ) (N.map κ) hMN hp
  have hc'' : (⟦pullbackPresentation (f ≫ toParameter K) (parameterQuotient K)⟧ : Points T 9 14) =
      ⟦presentation T 9 14 ((M.map κ).map h.appTop.hom) ((N.map κ).map h.appTop.hom)
        (rightInverse_map h.appTop.hom (M.map κ) (N.map κ) hMN)⟧ := by
    rw [hf]
    exact hc.trans hc'
  obtain ⟨d₂, hd₂⟩ := LagrangianGrassmannian.presentation_isomorphic_of_class_eq hc''
  obtain ⟨d₁, hd₁⟩ := LagrangianPluckerTrivialization.pullbackPresentation_comp_isomorphic
    (toParameter K) f (parameterQuotient K)
  refine ⟨d₁ ≪≫ d₂, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, hd₁, hd₂]
  change Stacks.FreeSheafMatrix.ofMatrix ((M.map κ).map h.appTop.hom) = _
  congr 1

variable [CharZero K]
attribute [local instance] LagrangianSymmetricPlucker.overBase globalSectionsModule

theorem rowSections_comparison {T : Scheme.{u}}
    (f : T ⟶ LagrangianLinearSections.ambient K)
    (M : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    (lineComparison K f).hom.app ⊤ (rowSections K f
      (Stacks.FreeSheafMatrix.ofMatrix
        (M.map (scalarMap K ((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K)))) j) =
      pullbackGlobalSections (f ≫ toLG K) (LagrangianPluckerQuotient.determinantLine K)
        (sectionLinear K (rowForms K M.mulVecLin j)) := by
  rw [rowSections, map_sum, pullback_rowSection, Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
  simp only [Scheme.Modules.Hom.app_smul, Matrix.map_apply, lineComparison_section]

/-- All-test original incidence factorization at the actual native point
of the original matrix is exactly vanishing of its original five sections. -/
theorem factorsThrough_iff_original_rows {T : Scheme.{u}}
    (f : T ⟶ LagrangianLinearSections.ambient K)
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
    (hf : f ≫ toParameter K =
      ((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K) ≫ matrixPoint K M hM) :
    (∃ z : T ⟶ family K, z ≫ inclusion K = f) ↔
      ∀ j : Fin 5, pullbackGlobalSections (f ≫ toLG K)
        (LagrangianPluckerQuotient.determinantLine K)
        (sectionLinear K (rowForms K M.mulVecLin j)) = 0 := by
  obtain ⟨d, hd⟩ := quotientFrame K f M hM hf
  rw [LagrangianIncidenceRows.factorsThrough_iff_rows K f d _ hd]
  apply forall_congr'
  intro j
  rw [← rowSections_comparison K f M j]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((lineComparison K f).hom.app ⊤)).injective).symm

end M9Native.LagrangianMatrixPointRows

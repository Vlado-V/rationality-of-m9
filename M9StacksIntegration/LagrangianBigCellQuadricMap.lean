module

public import M9StacksIntegration.LagrangianBigCellQuadricCoordinates
public import M9StacksIntegration.LagrangianPolynomialPluckerFrame
public import M9StacksIntegration.NativeProjectiveChartEvaluation

/-! The actual original LG big-cell morphism, followed by the original
polynomial Plucker embedding, is the genuine native normalized a-chart
graph map. This is an equality of scheme morphisms over every test ring. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianBigCellQuadricMap

open LagrangianBigCellQuadricCoordinates
open LagrangianQuadricChartReindex (aIndex)
open LagrangianGrassmannian LagrangianMatrixChart
open LagrangianPolynomialPluckerFrame

variable (K : Type u) [Field K]

theorem sectionPolynomial_a : MukaiConormalBigCellSections.sectionPolynomial K aIndex = 1 := by
  have h := blockGraphEvaluation_X K (Sum.inl ())
  exact h.symm.trans (blockGraphEvaluation_a K)

theorem sectionPolynomial_span : Ideal.span
    (Set.range (MukaiConormalBigCellSections.sectionPolynomial K)) = ⊤ :=
  NativeProjectiveChartEvaluation.normalized_span aIndex _ (sectionPolynomial_a K)

theorem nativeChartGraphMap_eq_eval : (nativeChartGraphMap K).toRingHom =
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun j : Fin 13 => MukaiConormalBigCellSections.sectionPolynomial K (aIndex.succAbove j)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval₂Hom_C]
    exact (nativeChartGraphMap K).commutes c
  · intro j
    rw [MvPolynomial.eval₂Hom_X']
    have h := RingHom.congr_fun (nativeChartGraphMap_comp_dehom K) (X (aIndex.succAbove j))
    change nativeChartGraphMap K (dehomCoeff K aIndex (X (aIndex.succAbove j))) = _ at h
    rw [dehomCoeff_eq_aeval, MvPolynomial.aeval_X, finSuccEquiv'_succAbove] at h
    simp only [Option.elim_some, MvPolynomial.eval₂Hom_X'] at h
    exact h

abbrev aOpen : (AlgebraicGeometry.Proj (polyGrading K 13)).Opens :=
  NativeProjectiveChartEvaluation.chartOpen (K := K) aIndex

def graphChartMap : Spec (.of (NativeRing K)) ⟶ (aOpen K).toScheme :=
  NativeProjectiveChartEvaluation.chartLift MvPolynomial.C aIndex
    (MukaiConormalBigCellSections.sectionPolynomial K)

theorem chartEvaluation_eq : NativeProjectiveChartEvaluation.chartEvaluation
    MvPolynomial.C aIndex (MukaiConormalBigCellSections.sectionPolynomial K) =
      (nativeChartGraphMap K).toRingHom.comp (sectionsChartEquiv K aIndex).symm.toRingHom := by
  rw [NativeProjectiveChartEvaluation.chartEvaluation, nativeChartGraphMap_eq_eval]

theorem chartEvaluation_surjective : Function.Surjective
    (NativeProjectiveChartEvaluation.chartEvaluation MvPolynomial.C aIndex
      (MukaiConormalBigCellSections.sectionPolynomial K)) := by
  rw [chartEvaluation_eq]
  exact (nativeChartGraphMap_surjective K).comp (sectionsChartEquiv K aIndex).symm.surjective

instance graphChartMap_isClosedImmersion : IsClosedImmersion (graphChartMap K) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (NativeProjectiveChartEvaluation.chartEvaluation MvPolynomial.C aIndex
        (MukaiConormalBigCellSections.sectionPolynomial K)))) :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective K)
  dsimp only [graphChartMap, NativeProjectiveChartEvaluation.chartLift]
  infer_instance

theorem graphChartMap_coordinate (F : MvPolynomial (Fin 13) K) :
    (graphChartMap K).appTop ((aOpen K).topIso.inv (sectionsChartEquiv K aIndex F)) =
      (Scheme.ΓSpecIso (.of (NativeRing K))).inv (nativeChartGraphMap K F) := by
  exact (NativeProjectiveChartEvaluation.chartLift_coordinate MvPolynomial.C aIndex
    (MukaiConormalBigCellSections.sectionPolynomial K) F).trans
      (congrArg (fun r : NativeRing K => (Scheme.ΓSpecIso (.of (NativeRing K))).inv r)
        (RingHom.congr_fun (nativeChartGraphMap_eq_eval K) F).symm)

variable [CharZero K]

/-- The native determinant frame computes the actual original Plucker
morphism, with the original normalized tuple and its original scalar map. -/
theorem bigCell_polynomialPlucker : bigCell K ≫ polynomialPlucker K =
    NativeProjectiveVector.point MvPolynomial.C
      (MukaiConormalBigCellSections.sectionPolynomial K) (sectionPolynomial_span K) := by
  let v := MukaiConormalBigCellSections.sectionPolynomial K
  let κ := (MukaiConormalBigCellSections.scalarEquiv K).toRingHom.comp MvPolynomial.C
  let w := (MukaiConormalBigCellSections.scalarEquiv K) ∘ v
  have hw : Ideal.span (Set.range w) = ⊤ := NativeProjectiveVector.span_map_eq_top
    (MukaiConormalBigCellSections.scalarEquiv K).toRingHom v (sectionPolynomial_span K)
  have hm := comp_polynomialPlucker_in_frame K (bigCell K)
    (MukaiConormalBigCellSections.determinantIso K) w hw
    (MukaiConormalBigCellSections.determinantIso_coordinate K)
  have hc : Stacks.ProjectiveSpaceChartRatio.baseRingHom (bigCell K ≫ projection K) = κ :=
    (coefficientMap_eq_baseRingHom K (bigCell K)).symm.trans
      (MukaiConormalBigCellSections.bigCell_coefficientMap K)
  rw [hc] at hm
  exact hm.trans (NativeProjectiveVector.point_eq_onScheme MvPolynomial.C v
    (sectionPolynomial_span K)).symm

/-- Equality of actual scheme morphisms in the native a-chart. No
projective-map equality, chart kernel, or isomorphism is a premise. -/
theorem graphChartMap_ambient : graphChartMap K ≫ (aOpen K).ι =
    bigCell K ≫ polynomialPlucker K := by
  exact (NativeProjectiveChartEvaluation.chartMap_eq_point MvPolynomial.C aIndex
    (MukaiConormalBigCellSections.sectionPolynomial K) (sectionPolynomial_a K)).trans
      (bigCell_polynomialPlucker K).symm

end M9Native.LagrangianBigCellQuadricMap

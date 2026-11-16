module

public import M9StacksIntegration.LagrangianBigCellQuadricMap
public import M9StacksIntegration.HomogeneousEquationChartMap
public import M9StacksIntegration.LagrangianTranslatedQuadricFamily

/-! The actual original native big-cell graph has precisely the
restricted ideal of the original twenty-one genuine quadratic sections.
The full scheme structure is obtained from the actual chart presentation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianBigCellQuadricKernel

open LagrangianBigCellQuadricCoordinates LagrangianBigCellQuadricMap
open LagrangianQuadricChartReindex (aIndex)

variable (K : Type u) [Field K]

def originalIdeal : (AlgebraicGeometry.Proj (polyGrading K 13)).IdealSheafData :=
  HomogeneousEquationChart.ideal K 13 2 (LagrangianPrimitiveQuadrics.form K)

/-- The genuine native chart kernel is identified with an actual
restricted quadratic ideal sheaf, with no kernel/formula premise. -/
theorem graphChartMap_kernel : (graphChartMap K).ker =
    (originalIdeal K).comap (aOpen K).ι := by
  let χ := (nativeChartGraphMap K).toRingHom
  have hχ := nativeChartGraphMap_surjective K
  have hker : RingHom.ker χ = HomogeneousEquationChart.chartIdeal K 13 2
      (LagrangianPrimitiveQuadrics.form K) aIndex := ker_nativeChartGraphMap K
  let c := HomogeneousEquationChartMap.ambientMap K 13 2 (LagrangianPrimitiveQuadrics.form K)
    aIndex (NativeRing K) χ hχ hker
  have hc : c = graphChartMap K := by
    apply NativeProjectiveChartEvaluation.eq_chartLift_of_coordinates MvPolynomial.C aIndex
      (MukaiConormalBigCellSections.sectionPolynomial K)
    intro F
    exact (HomogeneousEquationChartMap.ambientMap_presentation K 13 2
      (LagrangianPrimitiveQuadrics.form K) aIndex (NativeRing K) χ hχ hker F).trans
        (congrArg (fun r : NativeRing K => (Scheme.ΓSpecIso (.of (NativeRing K))).inv r)
          (RingHom.congr_fun (nativeChartGraphMap_eq_eval K) F))
  have hk := HomogeneousEquationChartMap.ambientMap_kernel K 13 2
    (LagrangianPrimitiveQuadrics.form K) aIndex (NativeRing K) χ hχ hker
  exact (congrArg (fun f : Spec (.of (NativeRing K)) ⟶ (aOpen K).toScheme => f.ker) hc).symm.trans hk

variable [CharZero K]

theorem originalIdeal_le_familyIdeal : originalIdeal K ≤ LagrangianTranslatedQuadricFamily.familyIdeal K := by
  apply iSup_le
  intro i
  exact LagrangianTranslatedQuadricFamily.original_le_familyIdeal K i

end M9Native.LagrangianBigCellQuadricKernel

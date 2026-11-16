module

public import M9StacksIntegration.LagrangianCommonKernelChartIso
public import M9StacksIntegration.LagrangianKernelTailMatrix
public import M9StacksIntegration.LagrangianKernelChartTriangle

/-!
# The actual five-section frames on the four original affine charts

The genuine determinant frame sends the actual five pulled sections to
their literal inverse-swapped polynomial minors. The original normalized polynomial functions are
proved to generate the actual unit ideal on every genuine affine chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite Matrix

universe u

namespace M9Native.LagrangianKernelAffineFiveSections

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open LagrangianAdmissibleCharts LagrangianCommonKernelChartAlgebra LagrangianKernelTailMatrix
open LagrangianTranslatedDeterminantSections LagrangianTranslatedFiveMinorSections
open LagrangianKernelFiveMinorNormalization LagrangianKernelFivePullback LagrangianKernelFiveSections
open LagrangianCommonKernelZero LagrangianKernelChartTriangle LagrangianKernelProjectiveComparison

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  LagrangianAdmissibleCharts.chart
  LagrangianKernelFivePullback.pulledFiveSections

variable (K : Type u) [Field K] [CharZero K]

/-- The actual original frame, pulled through the genuine zero-chart isomorphism. -/
theorem determinantFrame_five (s : LagrangianAdmissibleMinors.Choice) (a : Fin 5) :
    (LagrangianCommonKernelChartIso.determinantFrame K s).hom.app ⊤
      (pulledFiveSections K (LagrangianCommonKernelChartIso.affineLGMap K s) a) =
      (Scheme.ΓSpecIso (.of (ThreeRing K))).inv
        (eraseHeadThree K (Matrix.det ((translatedMatrix K (swap K s)⁻¹).submatrix id (fiveMinor a)))) := by
  change LinearIncidenceTensorCoordinates.unitCoordinate _
    ((LineFramePullback.pullbackFrame (LagrangianCommonKernelChartIso.tailMap K)
      ((Scheme.Modules.pullback (LagrangianAdmissibleCharts.chart K s)).obj (determinantLine K))
      (translatedDeterminantIso K (swap K s)⁻¹)).hom.app ⊤
      (((Scheme.Modules.pullbackComp (LagrangianCommonKernelChartIso.tailMap K)
        (LagrangianAdmissibleCharts.chart K s)).inv.app (determinantLine K)).app ⊤
        (pullbackGlobalSections (LagrangianCommonKernelChartIso.tailMap K ≫
          LagrangianAdmissibleCharts.chart K s) (determinantLine K) (ambientFiveSections K a)))) = _
  rw [LineFramePullback.pullbackComp_inv_apply,
    LineFramePullback.pullbackFrame_coordinate, ambientFiveSections]
  calc
    _ = (LagrangianCommonKernelChartIso.tailMap K).appTop
        (MukaiConormalBigCellSections.scalarEquiv K
          (Matrix.det ((translatedMatrix K (swap K s)⁻¹).submatrix id (fiveMinor a)))) :=
      congrArg (fun r : Γ(LagrangianCommonKernelChartIdeal.chartSpace K, ⊤) =>
        (LagrangianCommonKernelChartIso.tailMap K).appTop r)
        (translatedDeterminantIso_minor K (swap K s)⁻¹ (fiveMinor a))
    _ = _ := LagrangianCommonKernelChartIso.tailMap_scalar K _

theorem erase_translatedMinor (s : LagrangianAdmissibleMinors.Choice) (a : Fin 5) :
    eraseHeadThree K (Matrix.det ((translatedMatrix K (swap K s)⁻¹).submatrix id (fiveMinor a))) =
      Matrix.det ((tailMatrix K s).submatrix id (fiveMinor a)) := by
  have hm : (tailMatrix K s).submatrix id (fiveMinor a) =
      ((translatedMatrix K (swap K s)⁻¹).submatrix id (fiveMinor a)).map (eraseHeadThree K).toRingHom := rfl
  rw [hm]
  exact RingHom.map_det (eraseHeadThree K).toRingHom
    ((translatedMatrix K (swap K s)⁻¹).submatrix id (fiveMinor a))

theorem minor_eq_fiveCoordinates (s : LagrangianAdmissibleMinors.Choice) (a : Fin 5) :
    Matrix.det ((tailMatrix K s).submatrix id (fiveMinor a)) =
      LagrangianCommonKernelQuadric.fiveCoordinates (ThreeRing K) (tailMatrix K s) a := by
  fin_cases a <;> rfl

theorem determinantFrame_five_choice (c : Fin 4) (a : Fin 5) :
    (LagrangianCommonKernelChartIso.determinantFrame K (choice c)).hom.app ⊤
      (pulledFiveSections K (LagrangianCommonKernelChartIso.affineLGMap K (choice c)) a) =
      (Scheme.ΓSpecIso (.of (ThreeRing K))).inv (fiveFormula K c a) := by
  rw [determinantFrame_five, erase_translatedMinor, minor_eq_fiveCoordinates]
  exact congrArg (fun p => (Scheme.ΓSpecIso (.of (ThreeRing K))).inv p)
    (congrFun (tailFive_formula K c) a)

def normalizedFunctions (c : Fin 4) : Fin 5 → Γ(Spec (.of (ThreeRing K)), ⊤) :=
  fun a => (Scheme.ΓSpecIso (.of (ThreeRing K))).inv (fiveFormula K c a)

theorem normalizedFunctions_span (c : Fin 4) :
    Ideal.span (Set.range (normalizedFunctions K c)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hp : normalizedFunctions K c (SplitQuadricAffineAlgebra.pivot c) = 1 := by
    rw [normalizedFunctions, fiveFormula_pivot, map_one]
  rw [← hp]
  exact Ideal.subset_span ⟨SplitQuadricAffineAlgebra.pivot c, rfl⟩


end M9Native.LagrangianKernelAffineFiveSections

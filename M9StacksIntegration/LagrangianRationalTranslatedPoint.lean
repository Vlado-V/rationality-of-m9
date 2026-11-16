module

public import M9StacksIntegration.LagrangianTranslatedCharts
public import M9StacksIntegration.LagrangianChartCotangent

/-! Actual rational field points on the original translated charts.
The original base triangle is retained and forces the chart point to be
rational over the same field, with no field-endomorphism substitution. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianRationalTranslatedPoint

open LagrangianGrassmannian LagrangianTranslatedCharts LagrangianSymplecticAction
open LagrangianChartCotangent

variable (K : Type u) [Field K]

theorem translatedBigCell_mul (g h : Matrix.symplecticGroup (Fin 3) K) :
    translatedBigCell K g ≫ action K h = translatedBigCell K (g*h) := by
  change (LagrangianMatrixChart.bigCell K ≫ action K g) ≫ action K h =
    LagrangianMatrixChart.bigCell K ≫ action K (g*h)
  rw [Category.assoc,action_mul]

theorem factor_action (z : Spec (.of K) ⟶ chart K)
    (g h : Matrix.symplecticGroup (Fin 3) K) :
    (z ≫ translatedBigCell K g) ≫ action K h =
      z ≫ translatedBigCell K (g*h) := by
  rw [Category.assoc,translatedBigCell_mul]

/-- The actual rational point factors through a translated chart at an
actual rational chart point. The latter base identity is derived. -/
theorem exists_rational_chart (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K = 𝟙 _) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) K) (z : Spec (.of K) ⟶ chart K),
      z ≫ translatedBigCell K g = p ∧ z ≫ chartProjection K = 𝟙 _ := by
  obtain ⟨g,z,hz⟩ := exists_translatedBigCell_point K p hp
  refine ⟨g,z,hz,?_⟩
  have hf : translatedBigCell K g ≫ projection K = chartProjection K :=
    translatedBigCell_projection K g
  calc
    z ≫ chartProjection K = z ≫ (translatedBigCell K g ≫ projection K) :=
      congrArg (fun f => z ≫ f) hf.symm
    _ = (z ≫ translatedBigCell K g) ≫ projection K := (Category.assoc _ _ _).symm
    _ = p ≫ projection K := congrArg (fun f => f ≫ projection K) hz
    _ = 𝟙 _ := hp

end M9Native.LagrangianRationalTranslatedPoint

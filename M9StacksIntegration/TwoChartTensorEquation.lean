module

public import M9StacksIntegration.FreeTwoProjectiveChartCoordinates
public import M9StacksIntegration.RightLineTensorFrame

/-!
# The original two-term Q-first tensor equation on both actual P1 charts

The base scheme and first module stay abstract. Native pullback-tensor,
pullback-composition and pullback-congruence comparisons, followed by the
actual original tautological line frames, compute the original tensor
section. No coordinate, tensor, or scalar compatibility is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
universe u

namespace M9Native.TwoChartTensorEquation
open FreeTwoProjectiveCharts LinearIncidenceTensorCoordinates
variable (X : Scheme.{u}) (E : X.Modules)

abbrev vectorBundle : (projectiveBundleSpace X).Modules :=
  (Scheme.Modules.pullback (projectiveBundleProjection X)).obj E

abbrev equationBundle : (projectiveBundleSpace X).Modules :=
  tensorObj (projectiveBundleSpace X) (vectorBundle X E) (tautologicalLine X)

/-- The literal sum of the original two pulled sections tensored with
the original actual tautological coordinates, Q first. -/
def equationSection (s : Fin 2 → Γ(E, ⊤)) : Γ(equationBundle X E, ⊤) :=
  ∑ j : Fin 2, tensorTop (projectiveBundleSpace X) (vectorBundle X E)
    (tautologicalLine X) (pullbackGlobalSections (projectiveBundleProjection X) E (s j))
      (tautCoordinate X j)

def vectorIso (i : Fin 2) :
    (Scheme.Modules.pullback (chart X i)).obj (vectorBundle X E) ≅
      (Scheme.Modules.pullback (toBase X)).obj E :=
  (Scheme.Modules.pullbackComp (chart X i) (projectiveBundleProjection X)).app E ≪≫
    (Scheme.Modules.pullbackCongr (chart_projection X i)).app E

theorem vectorIso_section (i : Fin 2) (s : Γ(E, ⊤)) :
    (vectorIso X E i).hom.app ⊤
      (pullbackGlobalSections (chart X i) (vectorBundle X E)
        (pullbackGlobalSections (projectiveBundleProjection X) E s)) =
      pullbackGlobalSections (toBase X) E s := by
  change (((Scheme.Modules.pullbackCongr (chart_projection X i)).hom.app E).app ⊤)
    ((((Scheme.Modules.pullbackComp (chart X i) (projectiveBundleProjection X)).hom.app E).app ⊤)
      (pullbackGlobalSections (chart X i) (vectorBundle X E)
        (pullbackGlobalSections (projectiveBundleProjection X) E s))) = _
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr]

/-- The actual Q-first tensor frame keeps the first module untrivialized. -/
def tensorFrame (i : Fin 2) :
    (Scheme.Modules.pullback (chart X i)).obj (equationBundle X E) ≅
      (Scheme.Modules.pullback (toBase X)).obj E :=
  RightLineTensorFrame.frame (chart X i) (vectorBundle X E) (tautologicalLine X)
    ((Scheme.Modules.pullback (toBase X)).obj E) (vectorIso X E i) (chartFrame X i)

theorem tensorFrame_term (i j : Fin 2) (s : Γ(E, ⊤)) :
    (tensorFrame X E i).hom.app ⊤
      (pullbackGlobalSections (chart X i) (equationBundle X E)
        (tensorTop (projectiveBundleSpace X) (vectorBundle X E) (tautologicalLine X)
          (pullbackGlobalSections (projectiveBundleProjection X) E s) (tautCoordinate X j))) =
      (if j=i then (1 : Γ(chartSpace X, ⊤)) else coordinate X) •
        pullbackGlobalSections (toBase X) E s := by
  rw [tensorFrame, RightLineTensorFrame.frame_apply, vectorIso_section]
  congr 1
  exact FreeTwoProjectiveChartCoordinates.chartFrame_coordinate X i j

/-- The true original tensor equation has the true original two-chart
coordinates, over the actual global-function commutative ring. -/
theorem tensorFrame_equationSection (i : Fin 2) (s : Fin 2 → Γ(E, ⊤)) :
    (tensorFrame X E i).hom.app ⊤
      (pullbackGlobalSections (chart X i) (equationBundle X E) (equationSection X E s)) =
      ∑ j : Fin 2, (if j=i then (1 : Γ(chartSpace X, ⊤)) else coordinate X) •
        pullbackGlobalSections (toBase X) E (s j) := by
  simp only [equationSection, map_sum, tensorFrame_term]

theorem tensorFrame_equation_zero (s : Fin 2 → Γ(E, ⊤)) :
    (tensorFrame X E 0).hom.app ⊤
      (pullbackGlobalSections (chart X 0) (equationBundle X E) (equationSection X E s)) =
      pullbackGlobalSections (toBase X) E (s 0) +
        coordinate X • pullbackGlobalSections (toBase X) E (s 1) := by
  rw [tensorFrame_equationSection]
  simp only [Fin.sum_univ_two, ite_true, show (1 : Fin 2) ≠ 0 by decide,
    ite_false, one_smul]

theorem tensorFrame_equation_one (s : Fin 2 → Γ(E, ⊤)) :
    (tensorFrame X E 1).hom.app ⊤
      (pullbackGlobalSections (chart X 1) (equationBundle X E) (equationSection X E s)) =
      pullbackGlobalSections (toBase X) E (s 1) +
        coordinate X • pullbackGlobalSections (toBase X) E (s 0) := by
  rw [tensorFrame_equationSection]
  simp only [Fin.sum_univ_two, show (0 : Fin 2) ≠ 1 by decide,
    ite_false, ite_true, one_smul]
  exact add_comm _ _

end M9Native.TwoChartTensorEquation

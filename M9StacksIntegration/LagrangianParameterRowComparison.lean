module

public import M9StacksIntegration.LagrangianIncidenceRows
public import M9StacksIntegration.LagrangianIncidenceFieldPoints
public import M9StacksIntegration.LagrangianSymmetricSectionsPullback

/-! Actual field-point quotient rows and original determinant-section
combinations. The scalar map is the original structural map to Spec K.
The quotient frame is derived from the actual native parameter chart;
no frame, row equality, rank, or coordinate comparison is an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open AlgebraicGeometry.Grassmannian AlgebraicGeometry.ProjectiveSpaceOfModule
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianIncidenceFieldPoints M9Native.LagrangianIncidenceRows
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianProjectiveLinearForms
open M9Native.LagrangianSymmetricPlucker
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open scoped BigOperators

universe u

namespace M9Native.LagrangianParameterRowComparison

variable (K : Type u) [Field K]

def scalarMap {T : Scheme.{u}} (h : T ⟶ Spec (.of K)) : K →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ h.appTop).hom

theorem scalarMap_comp {T U : Scheme.{u}} (h : T ⟶ Spec (.of K)) (t : U ⟶ T) :
    scalarMap K (t ≫ h) = t.appTop.hom.comp (scalarMap K h) := by
  ext a
  rfl

theorem parameterChartMatrix_pullback {T : Scheme.{u}} (h : T ⟶ Spec (.of K))
    (ι : Fin 5 ↪ Fin 14)
    (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (ChartIndex.{u} (k := 9) (n := 14) ι) (ULift.{u} ℤ)))) :
    Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι (h ≫ g)) =
      (parameterChartMatrix K ι g).map (scalarMap K h) := by
  have hm : Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι (h ≫ g)) =
      (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι g)).map h.appTop.hom := by
    rw [toMatrix_chartQuotientMap, toMatrix_chartQuotientMap, ← chartMatrix_map]
    rfl
  rw [hm]
  ext j i
  change h.appTop (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι g) j i) =
    h.appTop ((Scheme.ΓSpecIso (.of K)).inv ((Scheme.ΓSpecIso (.of K)).hom
      (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι g) j i)))
  rw [(Scheme.ΓSpecIso (.of K)).hom_inv_id_apply]

variable [CharZero K]
attribute [local instance] LagrangianSymmetricPlucker.overBase globalSectionsModule

theorem pullback_rowSection {T : Scheme.{u}} (t : T ⟶ LagrangianGrassmannian.space K)
    (A : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    pullbackGlobalSections t (LagrangianPluckerQuotient.determinantLine K)
      (sectionLinear K (rowForms K A.mulVecLin j)) =
      ∑ i : Fin 14, scalarMap K (t ≫ LagrangianGrassmannian.projection K) (A j i) •
        pullbackGlobalSections t (LagrangianPluckerQuotient.determinantLine K)
          (LagrangianPluckerQuotient.primitiveSections K i) := by
  rw [sectionLinear_matrix_row, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change pullbackGlobalSections t (LagrangianPluckerQuotient.determinantLine K)
      (scalarMap K (LagrangianGrassmannian.projection K) (A j i) •
        LagrangianPluckerQuotient.primitiveSections K i) = _
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul, scalarMap_comp]
  rfl

def lineComparison {T : Scheme.{u}} (f : T ⟶ LagrangianLinearSections.ambient K) :
    (Scheme.Modules.pullback f).obj (lineBundle K) ≅
      (Scheme.Modules.pullback (f ≫ toLG K)).obj (LagrangianPluckerQuotient.determinantLine K) :=
  (Scheme.Modules.pullbackComp f (toLG K)).app (LagrangianPluckerQuotient.determinantLine K)

theorem lineComparison_section {T : Scheme.{u}} (f : T ⟶ LagrangianLinearSections.ambient K)
    (i : Fin 14) :
    (lineComparison K f).hom.app ⊤ (pullbackGlobalSections f (lineBundle K) (lineSection K i)) =
      pullbackGlobalSections (f ≫ toLG K) (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianPluckerQuotient.primitiveSections K i) :=
  AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp f (toLG K) _ _

theorem rowSections_comparison {T : Scheme.{u}} (f : T ⟶ LagrangianLinearSections.ambient K)
    (ι : Fin 5 ↪ Fin 14)
    (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (ChartIndex.{u} (k := 9) (n := 14) ι) (ULift.{u} ℤ)))) (j : Fin 5) :
    (lineComparison K f).hom.app ⊤ (rowSections K f
      (chartQuotientMap 9 14 ι (((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K) ≫ g)) j) =
      pullbackGlobalSections (f ≫ toLG K) (LagrangianPluckerQuotient.determinantLine K)
        (sectionLinear K (rowForms K (parameterChartMatrix K ι g).mulVecLin j)) := by
  rw [rowSections, map_sum, pullback_rowSection, parameterChartMatrix_pullback]
  simp only [Scheme.Modules.Hom.app_smul, Matrix.map_apply, lineComparison_section]

/-- The original incidence zero scheme and the actual quotient plane
have the same all-test factorization condition over the prescribed point. -/
theorem fixedPoint_factorsThrough_iff_plane {T : Scheme.{u}}
    (p : Spec (.of K) ⟶ parameter K) (ι : Fin 5 ↪ Fin 14)
    (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (ChartIndex.{u} (k := 9) (n := 14) ι) (ULift.{u} ℤ))))
    (hp : p ≫ GrassmannianCharts.toIntegral K 9 14 = g ≫ chart 9 14 ι)
    (f : T ⟶ LagrangianLinearSections.ambient K)
    (hf : f ≫ toParameter K = ((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K) ≫ p) :
    (∃ z : T ⟶ family K, z ≫ inclusion K = f) ↔
      (∃ z : T ⟶ projectiveSpaceOfModule K
        (Forms K ⧸ constraints K (parameterChartMatrix K ι g).mulVecLin),
        z ≫ quotientMap K (Forms K) (constraints K (parameterChartMatrix K ι g).mulVecLin) =
          (f ≫ toLG K) ≫ LagrangianPlucker.primitivePlucker K ≫ (coordinateIso K).hom) := by
  let q := chartQuotientMap 9 14 ι
    ((((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K)) ≫ g)
  have hfg : (f ≫ toParameter K) ≫ GrassmannianCharts.toIntegral K 9 14 =
      ((((f ≫ toLG K) ≫ LagrangianGrassmannian.projection K)) ≫ g) ≫ chart 9 14 ι := by
    rw [hf, Category.assoc, hp, ← Category.assoc]
  obtain ⟨d, hd⟩ := LagrangianLinearSectionQuotientCharts.pullback_ambient_chart_isomorphic K f ι _ hfg
  rw [LagrangianIncidenceRows.factorsThrough_iff_rows K f d q hd,
    LagrangianSymmetricSectionsPullback.originalPlucker_factorsThrough_iff]
  apply forall_congr'
  intro j
  rw [← rowSections_comparison K f ι g j]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((lineComparison K f).hom.app ⊤)).injective).symm

end M9Native.LagrangianParameterRowComparison

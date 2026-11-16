module

public import M9StacksIntegration.LagrangianCrossFieldParameter
public import M9StacksIntegration.LagrangianDeterminantFieldRows
public import M9StacksIntegration.LagrangianParameterRowComparison

/-! On every test scheme, original incidence factorization at a genuine
extension-field point is equivalent to the native L-incidence condition.
Both quotient frames are derived from the same actual integral chart;
the true determinant transport proves equality of the original rows. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianIncidenceRows M9Native.LagrangianParameterRowComparison
open M9Native.LagrangianIncidenceFieldPoints
open scoped BigOperators

universe u

namespace M9Native.LagrangianCrossFieldRows

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)
variable (p : Spec (.of L) ⟶ parameter K)
variable (hp : p ≫ parameterProjection K = GrassmannianFieldBaseChange.specMap φ)

def nativeAmbient : LagrangianGrassmannian.space L ⟶ LagrangianLinearSections.ambient L :=
  LagrangianFibreFactorization.fixedAmbient L (LagrangianCrossFieldParameter.parameterPoint p)
    (LagrangianCrossFieldParameter.parameterPoint_projection p) (𝟙 _)

@[reassoc (attr := simp)] theorem nativeAmbient_toLG : nativeAmbient p ≫ toLG L = 𝟙 _ :=
  LagrangianFibreFactorization.fixedAmbient_toLG _ _ _ _

@[reassoc (attr := simp)] theorem nativeAmbient_toParameter :
    nativeAmbient p ≫ toParameter L =
      LagrangianGrassmannian.projection L ≫ LagrangianCrossFieldParameter.parameterPoint p := by
  simpa only [nativeAmbient, Category.id_comp] using
    (LagrangianFibreFactorization.fixedAmbient_toParameter L
      (LagrangianCrossFieldParameter.parameterPoint p)
      (LagrangianCrossFieldParameter.parameterPoint_projection p) (𝟙 _))

theorem comp_nativeAmbient {T : Scheme.{u}} (f : T ⟶ LagrangianGrassmannian.space L) :
    f ≫ nativeAmbient p = LagrangianFibreFactorization.fixedAmbient L
      (LagrangianCrossFieldParameter.parameterPoint p)
      (LagrangianCrossFieldParameter.parameterPoint_projection p) f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, nativeAmbient_toLG, Category.comp_id,
      LagrangianFibreFactorization.fixedAmbient_toLG]
  · simp only [Category.assoc, nativeAmbient_toParameter,
      LagrangianFibreFactorization.fixedAmbient_toParameter]

variable [CharZero K]

theorem factorizations_iff {T : Scheme.{u}} (f : T ⟶ LagrangianGrassmannian.space L) :
    (∃ z : T ⟶ family K, z ≫ inclusion K = f ≫ LagrangianCrossFieldParameter.toAmbient φ p hp) ↔
      (∃ z : T ⟶ family L, z ≫ inclusion L = f ≫ nativeAmbient p) := by
  let _ : CharZero L := LagrangianDeterminantFieldRows.target_charZero φ
  obtain ⟨ι, g, hg⟩ := exists_integralChart_factor L
    (p ≫ GrassmannianCharts.toIntegral K 9 14)
  let aK := f ≫ LagrangianCrossFieldParameter.toAmbient φ p hp
  let aL := f ≫ nativeAmbient p
  let q := AlgebraicGeometry.Grassmannian.chartQuotientMap 9 14 ι
    ((f ≫ LagrangianGrassmannian.projection L) ≫ g)
  have hK : (aK ≫ toParameter K) ≫ GrassmannianCharts.toIntegral K 9 14 =
      ((f ≫ LagrangianGrassmannian.projection L) ≫ g) ≫
        AlgebraicGeometry.Grassmannian.chart 9 14 ι := by
    simp only [aK, Category.assoc, LagrangianCrossFieldParameter.toAmbient_toParameter]
    rw [hg]
  have hL : (aL ≫ toParameter L) ≫ GrassmannianCharts.toIntegral L 9 14 =
      ((f ≫ LagrangianGrassmannian.projection L) ≫ g) ≫
        AlgebraicGeometry.Grassmannian.chart 9 14 ι := by
    simp only [aL, Category.assoc, nativeAmbient_toParameter,
      LagrangianCrossFieldParameter.parameterPoint_toIntegral]
    rw [hg]
  obtain ⟨dK, hdK⟩ := LagrangianLinearSectionQuotientCharts.pullback_ambient_chart_isomorphic K aK ι _ hK
  obtain ⟨dL, hdL⟩ := LagrangianLinearSectionQuotientCharts.pullback_ambient_chart_isomorphic L aL ι _ hL
  rw [LagrangianIncidenceRows.factorsThrough_iff_rows K aK dK q hdK,
    LagrangianIncidenceRows.factorsThrough_iff_rows L aL dL q hdL]
  apply forall_congr'
  intro j
  have hKr : rowSections K aK q j = 0 ↔
      (∑ i : Fin 14, Stacks.FreeSheafMatrix.toMatrix q j i •
        pullbackGlobalSections (f ≫ LagrangianFieldBaseChange.map φ)
          (LagrangianPluckerQuotient.determinantLine K) (LagrangianPluckerQuotient.primitiveSections K i)) = 0 := by
    rw [← map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((lineComparison K aK).hom.app ⊤)).injective]
    simp only [rowSections, map_sum, Scheme.Modules.Hom.app_smul, lineComparison_section]
    dsimp only [aK]
    rw [Category.assoc, LagrangianCrossFieldParameter.toAmbient_toLG]
  have hLr : rowSections L aL q j = 0 ↔
      (∑ i : Fin 14, Stacks.FreeSheafMatrix.toMatrix q j i •
        pullbackGlobalSections f (LagrangianPluckerQuotient.determinantLine L)
          (LagrangianPluckerQuotient.primitiveSections L i)) = 0 := by
    rw [← map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((lineComparison L aL).hom.app ⊤)).injective]
    simp only [rowSections, map_sum, Scheme.Modules.Hom.app_smul, lineComparison_section]
    dsimp only [aL]
    rw [Category.assoc, nativeAmbient_toLG, Category.comp_id]
  exact hKr.trans ((LagrangianDeterminantFieldRows.row_zero_iff φ f
    (fun i => Stacks.FreeSheafMatrix.toMatrix q j i)).trans hLr.symm)

end M9Native.LagrangianCrossFieldRows

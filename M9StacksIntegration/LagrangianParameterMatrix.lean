module

public import M9StacksIntegration.LagrangianIncidenceFieldPoints
public import M9StacksIntegration.SplitMatrixGrassmannianNaturality

/-! Every actual rational parameter point is represented by an actual
surjective five by fourteen field matrix. This is derived from the native
normalized quotient charts and the actual representing equivalence. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianIncidenceFieldPoints M9Native.SplitMatrixGrassmannian

universe u

namespace M9Native.LagrangianParameterMatrix

variable (K : Type u) [Field K]

theorem exists_matrix (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _) :
    ∃ (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec),
      p = fieldPoint 9 14 K M hM := by
  obtain ⟨ι, g, hg⟩ := exists_integralChart_factor K
    (p ≫ GrassmannianCharts.toIntegral K 9 14)
  let M := parameterChartMatrix K ι g
  have hM : Function.Surjective M.mulVec := parameterChartMatrix_surjective K ι g
  obtain ⟨e, he⟩ := LagrangianLinearSectionQuotientCharts.pullback_parameter_chart_isomorphic
    K p ι g hg
  have hm : chartQuotientMap 9 14 ι g = (fieldPresentation 9 14 K M hM).map := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [fieldPresentation_matrix]
    ext j i
    change Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι g) j i =
      (Scheme.ΓSpecIso (.of K)).inv ((Scheme.ΓSpecIso (.of K)).hom
        (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι g) j i))
    exact ((Scheme.ΓSpecIso (.of K)).hom_inv_id_apply _).symm
  have hc : (functorData 9 14).objEquiv (Spec (.of K))
      ((schemeRepresentableBy 9 14).homEquiv (p ≫ GrassmannianCharts.toIntegral K 9 14)) =
        ⟦fieldPresentation 9 14 K M hM⟧ := by
    rw [← LagrangianLinearSectionQuotientCharts.pullback_parameter_class K p]
    exact Quotient.sound (.rel _ _ ⟨e, he.trans hm⟩)
  refine ⟨M, hM, ?_⟩
  apply pullback.hom_ext
  · exact hp.trans (fieldPoint_projection 9 14 K M hM).symm
  · apply (schemeRepresentableBy 9 14).homEquiv.injective
    apply ((functorData 9 14).objEquiv (Spec (.of K))).injective
    exact hc.trans (fieldPoint_class 9 14 K M hM).symm

end M9Native.LagrangianParameterMatrix

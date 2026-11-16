module
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing

public import M9StacksIntegration.LagrangianLinearSections
public import M9StacksIntegration.LagrangianPluckerTrivialization

/-! Actual rank-five universal quotient triangles on the universal linear-section charts.
The native representability adapter is the same proved naturality argument as the
frozen LG adapter, with the genuine rank-five parameter quotient retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.LagrangianLinearSectionQuotientCharts
open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerTrivialization

variable (K : Type u) [Field K]

theorem pullback_integral_class {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Grassmannian.scheme.{u} 9 14) :
    (⟦pullbackPresentation f integralParameterQuotient⟧ : Points T 9 14)=
      (functorData 9 14).objEquiv T ((schemeRepresentableBy 9 14).homEquiv f) := by
  change pullbackPointsMap f 9 14 (⟦integralParameterQuotient⟧ : Points _ 9 14)=_
  rw [show (⟦integralParameterQuotient⟧ : Points _ 9 14)=integralParameterClass from Quotient.out_eq _]
  rw [integralParameterClass,← pointsEquiv_map]
  congr 1
  simpa only [Category.comp_id] using ((schemeRepresentableBy 9 14).homEquiv_comp f (𝟙 _)).symm

theorem pullback_parameter_class {T : Scheme.{u}} (f : T ⟶ parameter K) :
    (⟦pullbackPresentation f (parameterQuotient K)⟧ : Points T 9 14)=
      (functorData 9 14).objEquiv T ((schemeRepresentableBy 9 14).homEquiv
        (f ≫ M9Native.GrassmannianCharts.toIntegral K 9 14)) := by
  change pullbackPointsMap f 9 14
    (pullbackPointsMap (M9Native.GrassmannianCharts.toIntegral K 9 14) 9 14
      (⟦integralParameterQuotient⟧ : Points _ 9 14))=_
  exact (congrFun (pullbackPointsMap_comp _ _ 9 14)
    (⟦integralParameterQuotient⟧ : Points _ 9 14)).symm.trans (pullback_integral_class _)

def chartPresentation {T : Scheme.{u}} (ι : Fin 5 ↪ Fin 14)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=9) (n:=14) ι) (ULift.{u} ℤ)))) :
    QuotientPresentation T 9 14 :=
  normalizedQuotientPresentation T 9 14 ι
    ((normalizedQuotientCoefficientsEquiv T 9 14 ι).symm (AffineSpace.toSpecMvPolyIntEquiv _ g))

theorem chartPresentation_map {T : Scheme.{u}} (ι : Fin 5 ↪ Fin 14)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=9) (n:=14) ι) (ULift.{u} ℤ)))) :
    (chartPresentation ι g).map=chartQuotientMap 9 14 ι g := by
  exact Eq.trans (Eq.refl ((chartPresentation ι g).map)) (Eq.refl _)

theorem pullback_parameter_chart_isomorphic {T : Scheme.{u}} (f : T ⟶ parameter K)
    (ι : Fin 5 ↪ Fin 14)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=9) (n:=14) ι) (ULift.{u} ℤ))))
    (hfg : f ≫ M9Native.GrassmannianCharts.toIntegral K 9 14=g ≫ chart 9 14 ι) :
    ∃ e : (pullbackPresentation f (parameterQuotient K)).target ≅ freeOn T 5,
      (pullbackPresentation f (parameterQuotient K)).map ≫ e.hom=chartQuotientMap 9 14 ι g := by
  have hclass : (⟦pullbackPresentation f (parameterQuotient K)⟧ : Points T 9 14)=
      ⟦chartPresentation ι g⟧ := by
    rw [pullback_parameter_class,hfg]
    exact objEquiv_homEquiv_comp_chartMap 9 14 ι g
  obtain ⟨e,he⟩ := presentation_isomorphic_of_class_eq hclass
  exact ⟨e,he.trans (chartPresentation_map ι g)⟩

theorem pullback_ambient_chart_isomorphic {T : Scheme.{u}} (f : T ⟶ ambient K)
    (ι : Fin 5 ↪ Fin 14)
    (g : T ⟶ Spec (.of (MvPolynomial (ChartIndex.{u} (k:=9) (n:=14) ι) (ULift.{u} ℤ))))
    (hfg : (f ≫ toParameter K) ≫ M9Native.GrassmannianCharts.toIntegral K 9 14=g ≫ chart 9 14 ι) :
    ∃ e : (pullbackPresentation f (ambientQuotient K)).target ≅ freeOn T 5,
      (pullbackPresentation f (ambientQuotient K)).map ≫ e.hom=chartQuotientMap 9 14 ι g := by
  obtain ⟨e₁,h₁⟩ := pullbackPresentation_comp_isomorphic (toParameter K) f (parameterQuotient K)
  obtain ⟨e₂,h₂⟩ := pullback_parameter_chart_isomorphic K (f ≫ toParameter K) ι g hfg
  refine ⟨e₁.trans e₂,?_⟩
  rw [Iso.trans_hom,← Category.assoc,h₁,h₂]

end M9Native.LagrangianLinearSectionQuotientCharts
end

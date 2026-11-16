module

public import M9StacksIntegration.LagrangianLinearSectionPolynomialCharts
public import M9StacksIntegration.LagrangianLinearSectionIdeals
public import M9StacksIntegration.LinearIncidenceJacobian

/-! The actual original incidence ideal on the actual polynomial product chart
is the genuine ideal of the five normalized linear equations. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local implicit_reducible] M9Native.LagrangianPlucker.matrixCover
  M9Native.GrassmannianCharts.matrixCover
namespace M9Native.LagrangianLinearSectionPolynomialIdeal
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianLinearSectionAmbientCharts M9Native.LagrangianLinearSectionPolynomialCharts
open M9Native.LagrangianLinearSectionEquations M9Native.LagrangianLinearSectionQuotientCharts
open M9Native.LinearIncidenceTensorCoordinates M9Native.FiniteFreeSectionIdeal
open AlgebraicGeometry.Grassmannian
variable (K : Type u) [Field K]

def integralPolynomialMap (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :=
  (chartPolynomialIso K ι κ).inv ≫ integralParameterChart K ι κ

theorem integralPolynomialMap_diagram (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (polynomialMap K ι κ ≫ toParameter K) ≫ M9Native.GrassmannianCharts.toIntegral K 9 14=
      integralPolynomialMap K ι κ ≫ chart 9 14 κ := by
  simpa only [polynomialMap,integralPolynomialMap,Category.assoc] using
    congrArg (fun h => (chartPolynomialIso K ι κ).inv ≫ h)
      (integralParameterChart_diagram K ι κ)

def polynomialQuotientIso (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (pullbackPresentation (polynomialMap K ι κ) (ambientQuotient K)).target ≅
      freeOn (Spec (.of (polynomialRing K ι κ))) 5 :=
  (pullback_ambient_chart_isomorphic K (polynomialMap K ι κ) κ
    (integralPolynomialMap K ι κ) (integralPolynomialMap_diagram K ι κ)).choose

theorem polynomialQuotientIso_fac (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (pullbackPresentation (polynomialMap K ι κ) (ambientQuotient K)).map ≫
      (polynomialQuotientIso K ι κ).hom=
        chartQuotientMap 9 14 κ (integralPolynomialMap K ι κ) :=
  (pullback_ambient_chart_isomorphic K (polynomialMap K ι κ) κ
    (integralPolynomialMap K ι κ) (integralPolynomialMap_diagram K ι κ)).choose_spec

theorem polynomial_equations (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 κ (integralPolynomialMap K ι κ))).mulVec
      (lineCoefficients K (polynomialMap K ι κ) (polynomialFrame K ι κ))=
        fun i => (Scheme.ΓSpecIso (.of (polynomialRing K ι κ))).inv
          (M9Native.LinearIncidenceJacobian.equations κ (baseCoefficients K ι) i) := by
  let φ := (Scheme.ΓSpecIso (.of (polynomialRing K ι κ))).inv.hom
  have hx : AffineSpace.toSpecMvPolyIntEquiv _ (integralPolynomialMap K ι κ)=
      fun j => φ (MvPolynomial.X j) := funext (polynomialMap_chartCoordinate K ι κ)
  have hv : lineCoefficients K (polynomialMap K ι κ) (polynomialFrame K ι κ)=
      fun j => φ (MvPolynomial.C (baseCoefficients K ι j)) :=
    funext (polynomialFrame_coefficients K ι κ)
  rw [toMatrix_chartQuotientMap,hx,chartMatrix_map,hv]
  exact funext fun i => (RingHom.map_mulVec φ
    (chartMatrix (k:=9) (n:=14) κ MvPolynomial.X)
      (fun j => MvPolynomial.C (baseCoefficients K ι j)) i).symm

/-- Equality of original ideal sheaves, not merely equality of their field-valued zero sets. -/
theorem polynomialIdeal_eq (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (ideal K).comap (polynomialMap K ι κ)=
      coordinateIdeal (polynomialRing K ι κ) 5
        (M9Native.LinearIncidenceJacobian.equations κ (baseCoefficients K ι)) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [M9Native.LagrangianLinearSectionIdeals.ideal_top K _
    (polynomialFrame K ι κ) (polynomialQuotientIso K ι κ) _ (polynomialQuotientIso_fac K ι κ),
      polynomial_equations,coordinateIdeal_top,Ideal.map_span,← Set.range_comp]
  rfl

abbrev familyChart (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :=
  pullback (polynomialMap K ι κ) (inclusion K)

def chartToFamily (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    familyChart K ι κ ⟶ family K := pullback.snd _ _

instance chartToFamily_isOpenImmersion (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    IsOpenImmersion (chartToFamily K ι κ) := by
  have : IsOpenImmersion (polynomialMap K ι κ) := by
    dsimp only [polynomialMap]
    infer_instance
  exact inferInstanceAs (IsOpenImmersion (pullback.snd (polynomialMap K ι κ) (inclusion K)))

def familyChartIsoQuotient (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    familyChart K ι κ ≅
      Spec (.of (M9Native.LinearIncidenceJacobian.Ring κ (baseCoefficients K ι))) :=
  ((ideal K).comapIso (polynomialMap K ι κ)).symm ≪≫
    eqToIso (congrArg (fun I : (Spec (.of (polynomialRing K ι κ))).IdealSheafData => I.subscheme)
      (polynomialIdeal_eq K ι κ)) ≪≫
        coordinateZeroSchemeIsoQuotient (polynomialRing K ι κ) 5
          (M9Native.LinearIncidenceJacobian.equations κ (baseCoefficients K ι))

@[reassoc] theorem familyChartIsoQuotient_inclusion (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (familyChartIsoQuotient K ι κ).hom ≫
      quotientInclusion (polynomialRing K ι κ) 5
        (M9Native.LinearIncidenceJacobian.equations κ (baseCoefficients K ι))=
      pullback.fst (polynomialMap K ι κ) (inclusion K) := by
  rw [familyChartIsoQuotient,Iso.trans_hom,Iso.trans_hom,Category.assoc,Category.assoc,
    coordinateZeroSchemeIsoQuotient_hom_inclusion]
  rw [eqToIso_subscheme_ι _ _ (polynomialIdeal_eq K ι κ)]
  exact Scheme.IdealSheafData.comapIso_inv_subschemeι _ _

@[reassoc] theorem familyChartIsoQuotient_over (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (familyChartIsoQuotient K ι κ).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(baseChart K ι,⊤)
        (M9Native.LinearIncidenceJacobian.Ring κ (baseCoefficients K ι))))=
      pullback.fst (polynomialMap K ι κ) (inclusion K) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C
          (σ:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
          (R:=Γ(baseChart K ι,⊤)))) := by
  have hc : Spec.map (CommRingCat.ofHom (algebraMap Γ(baseChart K ι,⊤)
      (M9Native.LinearIncidenceJacobian.Ring κ (baseCoefficients K ι))))=
      quotientInclusion (polynomialRing K ι κ) 5
        (M9Native.LinearIncidenceJacobian.equations κ (baseCoefficients K ι)) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C
            (σ:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
            (R:=Γ(baseChart K ι,⊤)))) :=
    Spec.map_comp (CommRingCat.ofHom (MvPolynomial.C
      (σ:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
      (R:=Γ(baseChart K ι,⊤))))
      (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span (Set.range (M9Native.LinearIncidenceJacobian.equations κ (baseCoefficients K ι))))))
  rw [hc,← Category.assoc,familyChartIsoQuotient_inclusion]

end M9Native.LagrangianLinearSectionPolynomialIdeal
end

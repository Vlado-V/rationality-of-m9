module

public import M9StacksIntegration.LagrangianLinearSectionPolynomialIdeal
public import M9StacksIntegration.LagrangianIntegral
public import M9StacksIntegration.ProperSmoothLocus

/-! Smoothness of the original total universal incidence, obtained from the
original polynomial chart ideals and their actual coefficient-localized Jacobians. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local implicit_reducible] M9Native.LagrangianPlucker.matrixCover
  M9Native.GrassmannianCharts.matrixCover M9Native.LagrangianLinearSectionAmbientCharts.ambientCover
namespace M9Native.LagrangianLinearSectionSmooth
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianLinearSectionAmbientCharts M9Native.LagrangianLinearSectionPolynomialCharts
open M9Native.LagrangianLinearSectionPolynomialIdeal
variable (K : Type u) [Field K]

def polynomialAmbientCover : (ambient K).OpenCover :=
  (ambientCover K).copy ChartIndexPair
    (fun j => Spec (.of (polynomialRing K j.1 j.2)))
    (fun j => polynomialMap K j.1 j.2) (Equiv.refl _)
    (fun j => (chartPolynomialIso K j.1 j.2).symm) (fun _ => rfl)

def polynomialFamilyCover : (family K).OpenCover := by
  let U : (family K).OpenCover := (polynomialAmbientCover K).pullback₁ (inclusion K)
  exact U.copy ChartIndexPair
    (fun j => familyChart K j.1 j.2) (fun j => chartToFamily K j.1 j.2)
    (Equiv.refl _) (fun j => pullbackSymmetry _ _) (fun _ => by
      exact (pullbackSymmetry_hom_comp_fst _ _).symm)

@[reassoc] theorem chartToFamily_toLG (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    chartToFamily K ι κ ≫ familyToLG K=
      (familyChartIsoQuotient K ι κ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(baseChart K ι,⊤)
          (M9Native.LinearIncidenceJacobian.Ring κ (baseCoefficients K ι)))) ≫
            (baseChart K ι).isoSpec.inv ≫ (M9Native.LagrangianPlucker.matrixCover K).f ι := by
  let X := baseChart K ι
  let l : X ⟶ M9Native.LagrangianGrassmannian.space K :=
    (M9Native.LagrangianPlucker.matrixCover K).f ι
  let p := pullback.fst (polynomialMap K ι κ) (inclusion K)
  let t := pullback.snd (polynomialMap K ι κ) (inclusion K)
  let r := Spec.map (CommRingCat.ofHom (MvPolynomial.C
    (σ:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
    (R:=Γ(X,⊤))))
  let q := Spec.map (CommRingCat.ofHom (algebraMap Γ(X,⊤)
    (M9Native.LinearIncidenceJacobian.Ring κ (baseCoefficients K ι))))
  let e := familyChartIsoQuotient K ι κ
  have hc : t ≫ inclusion K=p ≫ polynomialMap K ι κ := pullback.condition.symm
  have hl : polynomialMap K ι κ ≫ toLG K=polynomialBase K ι κ ≫ l :=
    polynomialMap_toLG K ι κ
  have hb : polynomialBase K ι κ=r ≫ X.isoSpec.inv := chartPolynomialIso_inv_over K ι κ
  have he : e.hom ≫ q=p ≫ r := familyChartIsoQuotient_over K ι κ
  change t ≫ inclusion K ≫ toLG K=e.hom ≫ q ≫ X.isoSpec.inv ≫ l
  calc
    _ = p ≫ polynomialMap K ι κ ≫ toLG K := by rw [← Category.assoc,hc,Category.assoc]
    _ = p ≫ polynomialBase K ι κ ≫ l := by rw [hl]
    _ = p ≫ r ≫ X.isoSpec.inv ≫ l := by rw [hb,Category.assoc]
    _ = e.hom ≫ q ≫ X.isoSpec.inv ≫ l := by rw [← Category.assoc,← he,Category.assoc]

theorem chart_smoothOfRelativeDimension [CharZero K]
    (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    SmoothOfRelativeDimension 40 (chartToFamily K ι κ ≫ familyToLG K) := by
  have : SmoothOfRelativeDimension 40
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(baseChart K ι,⊤)
        (M9Native.LinearIncidenceJacobian.Ring κ (baseCoefficients K ι))))) :=
    M9Native.LinearIncidenceJacobian.projection_smoothOfRelativeDimension κ
      (baseCoefficients K ι) (baseCoefficients_span K ι)
  have h₁ : SmoothOfRelativeDimension 40
      ((familyChartIsoQuotient K ι κ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(baseChart K ι,⊤)
          (M9Native.LinearIncidenceJacobian.Ring κ (baseCoefficients K ι))))) :=
    smoothOfRelativeDimension_comp (f:=(familyChartIsoQuotient K ι κ).hom) (n:=0) (m:=40) _
  have h₂ : SmoothOfRelativeDimension 0
      ((baseChart K ι).isoSpec.inv ≫ (M9Native.LagrangianPlucker.matrixCover K).f ι) := inferInstance
  rw [chartToFamily_toLG,← Category.assoc]
  exact smoothOfRelativeDimension_comp (n:=40) (m:=0) _ _

/-- The original incidence projection to LG is smooth of relative dimension forty. -/
instance familyToLG_smoothOfRelativeDimension [CharZero K] :
    SmoothOfRelativeDimension 40 (familyToLG K) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 40 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P:=@SmoothOfRelativeDimension 40)
    (polynomialFamilyCover K) ?_
  intro j
  change ChartIndexPair at j
  exact chart_smoothOfRelativeDimension K j.1 j.2

instance familyToLG_smooth [CharZero K] : Smooth (familyToLG K) :=
  SmoothOfRelativeDimension.smooth 40 _

def absoluteProjection : family K ⟶ Spec (.of K) := familyProjection K ≫ parameterProjection K

instance absoluteProjection_smoothOfRelativeDimension [CharZero K] :
    SmoothOfRelativeDimension 46 (absoluteProjection K) := by
  rw [absoluteProjection,← family_over]
  exact smoothOfRelativeDimension_comp (n:=40) (m:=6) _ _

instance absoluteProjection_smooth [CharZero K] : Smooth (absoluteProjection K) :=
  SmoothOfRelativeDimension.smooth 46 _

end M9Native.LagrangianLinearSectionSmooth
end

module

public import M9StacksIntegration.LagrangianLinearSectionAmbientCharts
public import M9StacksIntegration.LineFramePullback

/-! The original incidence coefficients on each actual product chart are pulled
from its actual LG-chart base ring. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.LagrangianLinearSectionPolynomialCharts
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianLinearSectionAmbientCharts M9Native.LagrangianLinearSectionLineCharts
open M9Native.LagrangianLinearSectionEquations M9Native.LinearIncidenceTensorCoordinates
open M9Native.LineFramePullback
variable (K : Type u) [Field K]

abbrev baseChart (ι : Fin 3 ↪ Fin 6) : Scheme.{u} :=
  (M9Native.LagrangianPlucker.matrixCover K).X ι

abbrev toBaseChart (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    chartSpace K ι κ ⟶ baseChart K ι := pullback.fst _ _

def baseFrame (ι : Fin 3 ↪ Fin 6) :=
  lineTrivialization K ((M9Native.LagrangianPlucker.matrixCover K).f ι) ι
    (M9Native.LagrangianPlucker.matrixChartIntegral K ι)
    (M9Native.LagrangianPlucker.matrixChartIntegral_diagram K ι)

def baseCoefficients (ι : Fin 3 ↪ Fin 6) : Fin 14 → Γ(baseChart K ι,⊤) :=
  M9Native.LagrangianPlucker.chartCoordinates K
    ((M9Native.LagrangianPlucker.matrixCover K).f ι) ι
      (M9Native.LagrangianPlucker.matrixChartIntegral K ι)

theorem baseCoefficients_span [CharZero K] (ι : Fin 3 ↪ Fin 6) :
    Ideal.span (Set.range (baseCoefficients K ι))=⊤ :=
  M9Native.LagrangianPlucker.chartCoordinates_span K
    ((M9Native.LagrangianPlucker.matrixCover K).f ι) ι
      (M9Native.LagrangianPlucker.matrixChartIntegral K ι)
        (M9Native.LagrangianPlucker.matrixChartIntegral_diagram K ι)

def constantFrame (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (Scheme.Modules.pullback (chartMap K ι κ)).obj (lineBundle K) ≅
      (SheafOfModules.unit (chartSpace K ι κ).ringCatSheaf : (chartSpace K ι κ).Modules) :=
  squareFrame (chartMap K ι κ) (toLG K) (toBaseChart K ι κ)
    ((M9Native.LagrangianPlucker.matrixCover K).f ι) (chartMap_toLG K ι κ)
      (M9Native.LagrangianPluckerQuotient.determinantLine K) (baseFrame K ι)

theorem constantFrame_coefficients (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) (j : Fin 14) :
    lineCoefficients K (chartMap K ι κ) (constantFrame K ι κ) j=
      (toBaseChart K ι κ).appTop (baseCoefficients K ι j) := by
  exact (squareFrame_coordinate (chartMap K ι κ) (toLG K) (toBaseChart K ι κ)
    ((M9Native.LagrangianPlucker.matrixCover K).f ι) (chartMap_toLG K ι κ)
      (M9Native.LagrangianPluckerQuotient.determinantLine K) (baseFrame K ι)
        (M9Native.LagrangianPluckerQuotient.primitiveSections K j)).trans
    (congrArg (toBaseChart K ι κ).appTop (lineTrivialization_sections K
      ((M9Native.LagrangianPlucker.matrixCover K).f ι) ι
        (M9Native.LagrangianPlucker.matrixChartIntegral K ι)
          (M9Native.LagrangianPlucker.matrixChartIntegral_diagram K ι) j))

@[reassoc] theorem chartPolynomialIso_inv_over (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (chartPolynomialIso K ι κ).inv ≫ toBaseChart K ι κ=
      Spec.map (CommRingCat.ofHom (MvPolynomial.C
        (σ:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
        (R:=Γ(baseChart K ι,⊤)))) ≫ (baseChart K ι).isoSpec.inv := by
  simp only [chartPolynomialIso,Iso.trans_inv,Category.assoc]
  rw [chartAffineIso_inv_fst,AffineSpace.isoOfIsAffine_inv_over]

theorem isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop=(Scheme.ΓSpecIso Γ(X,⊤)).inv := by
  have h := congrArg (fun φ : X ⟶ X => φ.appTop) X.isoSpec.hom_inv_id
  change X.isoSpec.inv.appTop ≫ X.toSpecΓ.appTop=𝟙 _ at h
  rw [Scheme.toSpecΓ_appTop] at h
  have h' := congrArg (fun φ => φ ≫ (Scheme.ΓSpecIso Γ(X,⊤)).inv) h
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,Category.id_comp] using h'

abbrev polynomialRing (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :=
  MvPolynomial (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ) Γ(baseChart K ι,⊤)

def polynomialMap (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    Spec (.of (polynomialRing K ι κ)) ⟶ ambient K :=
  (chartPolynomialIso K ι κ).inv ≫ chartMap K ι κ

def polynomialBase (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    Spec (.of (polynomialRing K ι κ)) ⟶ baseChart K ι :=
  (chartPolynomialIso K ι κ).inv ≫ toBaseChart K ι κ

theorem polynomialBase_appTop (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14)
    (r : Γ(baseChart K ι,⊤)) :
    (polynomialBase K ι κ).appTop r=
      (Scheme.ΓSpecIso (.of (polynomialRing K ι κ))).inv (MvPolynomial.C r) := by
  have ho := congrArg (fun h => h.appTop r) (chartPolynomialIso_inv_over K ι κ)
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MvPolynomial.C
      (σ:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
        (R:=Γ(baseChart K ι,⊤))))) r
  have hi := ConcreteCategory.congr_hom (isoSpec_inv_appTop (baseChart K ι)) r
  exact ho.trans ((congrArg (Spec.map (CommRingCat.ofHom (MvPolynomial.C
    (σ:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
      (R:=Γ(baseChart K ι,⊤))))).appTop hi).trans hn.symm)

theorem polynomialMap_toLG (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    polynomialMap K ι κ ≫ toLG K=
      polynomialBase K ι κ ≫ (M9Native.LagrangianPlucker.matrixCover K).f ι := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun h => (chartPolynomialIso K ι κ).inv ≫ h) (chartMap_toLG K ι κ))

def polynomialFrame (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (Scheme.Modules.pullback (polynomialMap K ι κ)).obj (lineBundle K) ≅
      (SheafOfModules.unit (Spec (.of (polynomialRing K ι κ))).ringCatSheaf :
        (Spec (.of (polynomialRing K ι κ))).Modules) :=
  squareFrame (polynomialMap K ι κ) (toLG K) (polynomialBase K ι κ)
    ((M9Native.LagrangianPlucker.matrixCover K).f ι) (polynomialMap_toLG K ι κ)
      (M9Native.LagrangianPluckerQuotient.determinantLine K) (baseFrame K ι)

theorem polynomialFrame_coefficients (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) (j : Fin 14) :
    lineCoefficients K (polynomialMap K ι κ) (polynomialFrame K ι κ) j=
      (Scheme.ΓSpecIso (.of (polynomialRing K ι κ))).inv (MvPolynomial.C (baseCoefficients K ι j)) := by
  exact (squareFrame_coordinate (polynomialMap K ι κ) (toLG K) (polynomialBase K ι κ)
    ((M9Native.LagrangianPlucker.matrixCover K).f ι) (polynomialMap_toLG K ι κ)
      (M9Native.LagrangianPluckerQuotient.determinantLine K) (baseFrame K ι)
        (M9Native.LagrangianPluckerQuotient.primitiveSections K j)).trans
    ((congrArg (polynomialBase K ι κ).appTop (lineTrivialization_sections K
      ((M9Native.LagrangianPlucker.matrixCover K).f ι) ι
        (M9Native.LagrangianPlucker.matrixChartIntegral K ι)
          (M9Native.LagrangianPlucker.matrixChartIntegral_diagram K ι) j)).trans
            (polynomialBase_appTop K ι κ _))

theorem chartAffineIso_inv_integral (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (chartAffineIso K ι κ).inv ≫ integralParameterChart K ι κ=
      AffineSpace.toSpecMvPoly
        (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ) (baseChart K ι) := by
  exact (congrArg (fun h => h ≫ AffineSpace.toSpecMvPoly
    (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ) (Spec (.of K)))
      (chartAffineIso_inv_snd K ι κ)).trans (AffineSpace.map_toSpecMvPoly _)

theorem polynomialMap_chartCoordinate (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14)
    (j : AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ) :
    AffineSpace.toSpecMvPolyIntEquiv _
      ((chartPolynomialIso K ι κ).inv ≫ integralParameterChart K ι κ) j=
        (Scheme.ΓSpecIso (.of (polynomialRing K ι κ))).inv (MvPolynomial.X j) := by
  have h := congrArg (fun f => AffineSpace.toSpecMvPolyIntEquiv _ f j)
    (chartAffineIso_inv_integral K ι κ)
  exact (congrArg ((AffineSpace.isoOfIsAffine _ (baseChart K ι)).inv.appTop) h).trans
    (AffineSpace.isoOfIsAffine_inv_appTop_coord _ j)

end M9Native.LagrangianLinearSectionPolynomialCharts
end

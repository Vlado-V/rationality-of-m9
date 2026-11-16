module

public import M9StacksIntegration.LagrangianLinearSectionLineCharts
public import M9StacksIntegration.LagrangianLinearSectionQuotientCharts

/-! The genuine affine product charts of the actual universal incidence ambient
scheme, and their actual determinant-line and rank-five quotient trivializations. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.LagrangianLinearSectionAmbientCharts
open M9Native.LagrangianLinearSections M9Native.LagrangianMatrixChart
open M9Native.LagrangianLinearSectionLineCharts M9Native.LagrangianLinearSectionQuotientCharts
open AlgebraicGeometry.Grassmannian
variable (K : Type u) [Field K]

theorem pullbackCongrHom_inv_fst {A B C : Scheme.{u}} {f₁ f₂ : A ⟶ C} {g₁ g₂ : B ⟶ C}
    (h₁ : f₁=f₂) (h₂ : g₁=g₂) :
    (pullback.congrHom h₁ h₂).inv ≫ pullback.fst f₁ g₁=pullback.fst f₂ g₂ := by
  rw [pullback.congrHom_inv]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem pullbackCongrHom_inv_snd {A B C : Scheme.{u}} {f₁ f₂ : A ⟶ C} {g₁ g₂ : B ⟶ C}
    (h₁ : f₁=f₂) (h₂ : g₁=g₂) :
    (pullback.congrHom h₁ h₂).inv ≫ pullback.snd f₁ g₁=pullback.snd f₂ g₂ := by
  rw [pullback.congrHom_inv]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

abbrev ChartIndexPair := (Fin 3 ↪ Fin 6) × (Fin 5 ↪ Fin 14)

def ambientCover : (ambient K).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (M9Native.LagrangianPlucker.matrixCover K)
    (M9Native.GrassmannianCharts.matrixCover K 9 14)
      (M9Native.LagrangianGrassmannian.projection K) (parameterProjection K)

abbrev chartSpace (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) : Scheme.{u} :=
  (ambientCover K).X (ι,κ)
abbrev chartMap (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) : chartSpace K ι κ ⟶ ambient K :=
  (ambientCover K).f (ι,κ)

instance chartMap_isOpenImmersion (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    IsOpenImmersion (chartMap K ι κ) := inferInstance

instance lagrangianMatrixChart_isAffine (ι : Fin 3 ↪ Fin 6) :
    IsAffine ((M9Native.LagrangianPlucker.matrixCover K).X ι) := by
  change IsAffine (pullback (M9Native.LagrangianGrassmannian.inclusion K)
    (M9Native.GrassmannianCharts.chartOver K 3 6 ι))
  infer_instance

instance chartSpace_isAffine (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    IsAffine (chartSpace K ι κ) := by
  change IsAffine (pullback
    ((M9Native.LagrangianPlucker.matrixCover K).f ι ≫ M9Native.LagrangianGrassmannian.projection K)
    (M9Native.GrassmannianCharts.chartOver K 9 14 κ ≫ parameterProjection K))
  infer_instance

@[reassoc] theorem chartMap_toLG (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    chartMap K ι κ ≫ toLG K=
      pullback.fst _ _ ≫ (M9Native.LagrangianPlucker.matrixCover K).f ι := by
  change pullback.map _ _ _ _ ((M9Native.LagrangianPlucker.matrixCover K).f ι)
    (M9Native.GrassmannianCharts.chartOver K 9 14 κ) (𝟙 _) (Category.comp_id _) (Category.comp_id _) ≫ pullback.fst _ _=_
  exact pullback.lift_fst _ _ _

@[reassoc] theorem chartMap_toParameter (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    chartMap K ι κ ≫ toParameter K=
      pullback.snd _ _ ≫ M9Native.GrassmannianCharts.chartOver K 9 14 κ := by
  change pullback.map _ _ _ _ ((M9Native.LagrangianPlucker.matrixCover K).f ι)
    (M9Native.GrassmannianCharts.chartOver K 9 14 κ) (𝟙 _) (Category.comp_id _) (Category.comp_id _) ≫ pullback.snd _ _=_
  exact pullback.lift_snd _ _ _

def integralLGChart (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) : chartSpace K ι κ ⟶
    Spec (.of (MvPolynomial (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=3) (n:=6) ι) (ULift.{u} ℤ))) :=
  pullback.fst _ _ ≫ M9Native.LagrangianPlucker.matrixChartIntegral K ι

def integralParameterChart (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) : chartSpace K ι κ ⟶
    Spec (.of (MvPolynomial (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ) (ULift.{u} ℤ))) :=
  pullback.snd _ _ ≫ pullback.snd (terminal.from (Spec (.of K)))
    (terminal.from (Spec (.of (MvPolynomial (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ) (ULift.{u} ℤ)))))

@[reassoc] theorem integralLGChart_diagram (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    ((chartMap K ι κ ≫ toLG K) ≫ M9Native.LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _=
      integralLGChart K ι κ ≫ chart 3 6 ι := by
  rw [chartMap_toLG]
  simpa only [Category.assoc,integralLGChart] using congrArg
    (fun h => pullback.fst _ _ ≫ h) (M9Native.LagrangianPlucker.matrixChartIntegral_diagram K ι)

@[reassoc] theorem integralParameterChart_diagram (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (chartMap K ι κ ≫ toParameter K) ≫ M9Native.GrassmannianCharts.toIntegral K 9 14=
      integralParameterChart K ι κ ≫ chart 9 14 κ := by
  rw [chartMap_toParameter]
  simpa only [Category.assoc,integralParameterChart] using congrArg
    (fun h => pullback.snd _ _ ≫ h) (M9Native.GrassmannianCharts.chartOver_toIntegral K 9 14 κ)

def lineIso (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :=
  ambientLineIso K (chartMap K ι κ) ι (integralLGChart K ι κ) (integralLGChart_diagram K ι κ)

theorem exists_quotientIso (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    ∃ e : (pullbackPresentation (chartMap K ι κ) (ambientQuotient K)).target ≅ freeOn (chartSpace K ι κ) 5,
      (pullbackPresentation (chartMap K ι κ) (ambientQuotient K)).map ≫ e.hom=
        chartQuotientMap 9 14 κ (integralParameterChart K ι κ) :=
  pullback_ambient_chart_isomorphic K (chartMap K ι κ) κ (integralParameterChart K ι κ)
    (integralParameterChart_diagram K ι κ)

/-- The original affine ambient chart is the actual affine space over its original LG chart. -/
def chartAffineIso (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    chartSpace K ι κ ≅ AffineSpace (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
      ((M9Native.LagrangianPlucker.matrixCover K).X ι) :=
  (pullback.congrHom rfl (M9Native.GrassmannianCharts.chartOver_projection K 9 14 κ)) ≪≫
    (AffineSpace.isPullback_map (n:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
      ((M9Native.LagrangianPlucker.matrixCover K).f ι ≫
        M9Native.LagrangianGrassmannian.projection K)).flip.isoPullback.symm

/-- The actual product chart is the spectrum of its actual polynomial algebra over the LG chart. -/
def chartPolynomialIso (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    chartSpace K ι κ ≅ Spec (.of (MvPolynomial
      (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
      Γ((M9Native.LagrangianPlucker.matrixCover K).X ι,⊤))) :=
  chartAffineIso K ι κ ≪≫
    AffineSpace.isoOfIsAffine _ ((M9Native.LagrangianPlucker.matrixCover K).X ι)

@[reassoc] theorem chartAffineIso_inv_fst (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (chartAffineIso K ι κ).inv ≫ pullback.fst _ _=
      (AffineSpace (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
        ((M9Native.LagrangianPlucker.matrixCover K).X ι) ↘
          ((M9Native.LagrangianPlucker.matrixCover K).X ι)) := by
  let hs := (AffineSpace.isPullback_map
    (n:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
    ((M9Native.LagrangianPlucker.matrixCover K).f ι ≫
      M9Native.LagrangianGrassmannian.projection K)).flip
  have hc := pullbackCongrHom_inv_fst
    (rfl : ((M9Native.LagrangianPlucker.matrixCover K).f ι ≫
      M9Native.LagrangianGrassmannian.projection K)=_)
        (M9Native.GrassmannianCharts.chartOver_projection K 9 14 κ)
  exact (congrArg (fun t => hs.isoPullback.hom ≫ t) hc).trans hs.isoPullback_hom_fst

@[reassoc] theorem chartAffineIso_inv_snd (ι : Fin 3 ↪ Fin 6) (κ : Fin 5 ↪ Fin 14) :
    (chartAffineIso K ι κ).inv ≫ pullback.snd _ _=
      AffineSpace.map (AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
        ((M9Native.LagrangianPlucker.matrixCover K).f ι ≫
          M9Native.LagrangianGrassmannian.projection K) := by
  let hs := (AffineSpace.isPullback_map
    (n:=AlgebraicGeometry.Grassmannian.ChartIndex.{u} (k:=9) (n:=14) κ)
    ((M9Native.LagrangianPlucker.matrixCover K).f ι ≫
      M9Native.LagrangianGrassmannian.projection K)).flip
  have hc := pullbackCongrHom_inv_snd
    (rfl : ((M9Native.LagrangianPlucker.matrixCover K).f ι ≫
      M9Native.LagrangianGrassmannian.projection K)=_)
        (M9Native.GrassmannianCharts.chartOver_projection K 9 14 κ)
  exact (congrArg (fun t => hs.isoPullback.hom ≫ t) hc).trans hs.isoPullback_hom_snd

/-- These are actual affine opens of the original family, not a substitute incidence model. -/
def familyCover : (family K).OpenCover := (ambientCover K).pullback₁ (inclusion K)

instance familyCover_isAffine (j : (familyCover K).I₀) : IsAffine ((familyCover K).X j) := by
  rcases j with ⟨ι,κ⟩
  have : IsAffine ((ambientCover K).X (ι,κ)) := chartSpace_isAffine K ι κ
  change IsAffine (pullback (inclusion K) ((ambientCover K).f (ι,κ)))
  infer_instance

end M9Native.LagrangianLinearSectionAmbientCharts
end

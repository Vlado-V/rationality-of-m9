module

public import M9.RadicalMapPolynomial
public import M9.Private.ProjectiveCharts

/-! # Genuine scheme morphisms for the polynomial radical charts

Each nonzero ambient-component chart is an actual affine localization. The
coordinate ratios induce an actual scheme morphism into native projective
thirteen-space. The coordinate vector will be the polynomial radical vector;
no existence or regularity of a radical map is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.RadicalMap

open CategoryTheory AlgebraicGeometry
open M9.ProjectiveGeometry

abbrev ComponentRing (r : Fin 14 → ChartRing ℂ) (k : Fin 14) := Localization.Away (r k)

/-- The actual source is the principal affine open on which this component is invertible. -/
def componentSourceToChart (r : Fin 14 → ChartRing ℂ) (k : Fin 14) :
    Spec (.of (ComponentRing r k)) ⟶ Spec (.of (ChartRing ℂ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ChartRing ℂ) (ComponentRing r k)))

instance componentSourceToChart_isOpenImmersion (r : Fin 14 → ChartRing ℂ) (k : Fin 14) :
    IsOpenImmersion (componentSourceToChart r k) :=
  IsOpenImmersion.of_isLocalization (r k)

theorem componentSourceToChart_range (r : Fin 14 → ChartRing ℂ) (k : Fin 14) :
    Set.range (componentSourceToChart r k) =
      (PrimeSpectrum.basicOpen (r k) : Set (PrimeSpectrum (ChartRing ℂ))) :=
  PrimeSpectrum.localization_away_comap_range (ComponentRing r k) (r k)

/-- The actual coordinate ring homomorphism, with the k-th projective coordinate normalized. -/
def componentRatioHom (r : Fin 14 → ChartRing ℂ) (k : Fin 14) :
    ProjectiveChartToPolynomial.projectiveChartPolynomial 13 k →ₐ[ℂ] ComponentRing r k :=
  MvPolynomial.aeval (fun j => algebraMap (ChartRing ℂ) (ComponentRing r k) (r j.val) *
    IsLocalization.Away.invSelf (r k))

@[simp] theorem componentRatioHom_X (r : Fin 14 → ChartRing ℂ) (k : Fin 14)
    (j : {j : Fin 14 // j ≠ k}) :
    componentRatioHom r k (MvPolynomial.X j) =
      algebraMap (ChartRing ℂ) (ComponentRing r k) (r j.val) * IsLocalization.Away.invSelf (r k) := by
  simp [componentRatioHom]

/-- A genuine regular map from the actual principal localization into native P13. -/
def componentSchemeMorphism (r : Fin 14 → ChartRing ℂ) (k : Fin 14) :
    Spec (.of (ComponentRing r k)) ⟶ ProjectiveSpace.projectiveSpace 13 :=
  Spec.map (CommRingCat.ofHom (componentRatioHom r k).toRingHom) ≫
    ProjectiveChart.projectiveAffineChartMap 13 k

/-- The regular chart map respects the actual complex structure morphisms. -/
theorem componentSchemeMorphism_over (r : Fin 14 → ChartRing ℂ) (k : Fin 14) :
    componentSchemeMorphism r k ≫ ProjectiveSpace.projectiveSpaceToBase 13 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ComponentRing r k))) := by
  rw [componentSchemeMorphism,Category.assoc,ProjectiveChart.projectiveAffineChartMap_over]
  rw [ProjectiveChart.projectiveChartPolynomialToBase,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (componentRatioHom r k).comp_algebraMap

/-- Literal field evaluation extends to the actual localization on its nonzero locus. -/
def componentEvaluation (r : Fin 14 → ChartRing ℂ) (k : Fin 14) (x : ChartIndex → ℂ)
    (hx : MvPolynomial.eval x (r k) ≠ 0) : ComponentRing r k →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (r k) (f := MvPolynomial.aeval x)
    (isUnit_iff_ne_zero.mpr hx)

@[simp] theorem componentEvaluation_algebraMap (r : Fin 14 → ChartRing ℂ) (k : Fin 14)
    (x : ChartIndex → ℂ) (hx : MvPolynomial.eval x (r k) ≠ 0) (f : ChartRing ℂ) :
    componentEvaluation r k x hx (algebraMap (ChartRing ℂ) (ComponentRing r k) f) =
      MvPolynomial.eval x f := by
  simp [componentEvaluation]

theorem componentEvaluation_invSelf (r : Fin 14 → ChartRing ℂ) (k : Fin 14)
    (x : ChartIndex → ℂ) (hx : MvPolynomial.eval x (r k) ≠ 0) :
    componentEvaluation r k x hx (IsLocalization.Away.invSelf (r k)) =
      (MvPolynomial.eval x (r k))⁻¹ := by
  have h := congrArg (componentEvaluation r k x hx)
    (IsLocalization.Away.mul_invSelf (S := ComponentRing r k) (r k))
  rw [map_mul,map_one,componentEvaluation_algebraMap] at h
  apply (mul_left_cancel₀ hx)
  rw [h,mul_inv_cancel₀ hx]

/-- The morphism's actual coordinate values are exactly the polynomial coordinate ratios. -/
theorem componentRatio_evaluation (r : Fin 14 → ChartRing ℂ) (k : Fin 14)
    (x : ChartIndex → ℂ) (hx : MvPolynomial.eval x (r k) ≠ 0)
    (j : {j : Fin 14 // j ≠ k}) :
    componentEvaluation r k x hx (componentRatioHom r k (MvPolynomial.X j)) =
      MvPolynomial.eval x (r j.val) / MvPolynomial.eval x (r k) := by
  rw [componentRatioHom_X,map_mul,componentEvaluation_algebraMap,
    componentEvaluation_invSelf,div_eq_mul_inv]

end M9.RadicalMap

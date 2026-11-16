module

public import M9StacksIntegration.SplitQuadricStandardCharts

/-!
# Actual coordinate maps of the split-quadric affine charts

These formulas retain the actual ambient projective morphism, not only
an abstract affine-three isomorphism. The coordinate functions are derived
from the original native chart presentation and the constructed ring maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.SplitQuadricChartCoordinates

open SplitQuadricLinearSection SplitQuadricAffineAlgebra SplitQuadricStandardCharts
open Stacks.ProjectiveChart

attribute [local implicit_reducible] SplitQuadricStandardCharts.chart

/-- The actual restriction morphism and native section identifications commute. -/
theorem morphismRestrict_scalar {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (r : Γ(Y, U)) : (f ∣_ U).appTop (U.topIso.inv r) =
      (f ⁻¹ᵁ U).topIso.inv ((f.app U) r) := by
  have ht : (f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ f.app U := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE_eq_app]
  have h : U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [CommRingCat.comp_apply] using ConcreteCategory.congr_hom h r

variable (K : Type u) [Field K]

abbrev ambientOpen (c : Fin 4) : (ambient K).Opens :=
  Proj.basicOpen (polyGrading K 4) (X (pivot c))

/-- The constructed affine isomorphism acts by the genuine chart ring equivalence. -/
theorem chartIso_inv_value (c : Fin 4) (r : Γ(quadric K, SplitQuadricStandardCharts.chart K c)) :
    (chartIsoAffineThree K c).inv.appTop ((SplitQuadricStandardCharts.chart K c).topIso.inv r) =
      (Scheme.ΓSpecIso (.of (PolynomialThree K))).inv
        (SplitQuadricStandardCharts.chartRingEquiv K c r) := by
  rw [chartIsoAffineThree, Iso.trans_inv, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (Spec.map (CommRingCat.ofHom (SplitQuadricStandardCharts.chartRingEquiv K c).toRingHom)).appTop
    ((chart_isAffineOpen K c).isoSpec.inv.appTop
      ((SplitQuadricStandardCharts.chart K c).topIso.inv r)) = _
  rw [IsAffineOpen.isoSpec_inv_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (SplitQuadricStandardCharts.chartRingEquiv K c).toRingHom)) r).symm

/-- The actual affine chart map into the actual ambient projective standard open. -/
def ambientChartMap (c : Fin 4) :
    Spec (.of (PolynomialThree K)) ⟶ (ambientOpen K c).toScheme :=
  (chartIsoAffineThree K c).inv ≫ (quadricInclusion K ∣_ ambientOpen K c)

@[reassoc] theorem ambientChartMap_inclusion (c : Fin 4) :
    ambientChartMap K c ≫ (ambientOpen K c).ι = affineThreeMap K c ≫ quadricInclusion K := by
  simp only [ambientChartMap, affineThreeMap, Category.assoc, morphismRestrict_ι]
  rfl

/-- Every actual ambient affine coordinate has the explicit original polynomial value. -/
theorem ambientChartMap_presentation (c : Fin 4) (p : PolynomialFour K) :
    (ambientChartMap K c).appTop
      ((ambientOpen K c).topIso.inv (sectionsChartEquiv K (pivot c) p)) =
      (Scheme.ΓSpecIso (.of (PolynomialThree K))).inv (chartMap K c p) := by
  rw [ambientChartMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hr := morphismRestrict_scalar (quadricInclusion K) (ambientOpen K c)
    (sectionsChartEquiv K (pivot c) p)
  exact (congrArg (fun r => (chartIsoAffineThree K c).inv.appTop r) hr).trans
    ((chartIso_inv_value K c (chartPresentation (quadricInclusion K) (pivot c) p)).trans
      (congrArg (fun r => (Scheme.ΓSpecIso (.of (PolynomialThree K))).inv r)
        (chartRingEquiv_presentation K c p)))

theorem ambientChartMap_variable (c : Fin 4) (j : Fin 4) :
    (ambientChartMap K c).appTop
      ((ambientOpen K c).topIso.inv (sectionsChartEquiv K (pivot c) (X j))) =
      (Scheme.ΓSpecIso (.of (PolynomialThree K))).inv (chartVariables K c j) := by
  rw [ambientChartMap_presentation, chartMap, MvPolynomial.aeval_X]

end M9Native.SplitQuadricChartCoordinates

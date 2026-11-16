module

public import M9StacksIntegration.NativeProjectiveVectorChart
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Dehomogenization

/-! Actual standard projective charts agree with the native projective
map of a normalized tuple over every commutative ring. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.ProjectiveChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.NativeProjectiveChartEvaluation

variable {K R : Type u} [CommRing K] [CommRing R]
  (κ : K →+* R) {n : ℕ} (p : Fin (n + 1)) (r : Fin (n + 1) → R)

/-- Evaluation of the actual dehomogenization is the original evaluation
when the pivot coordinate is one. -/
theorem eval₂_comp_dehomCoeff (hr : r p = 1) :
    (eval₂Hom κ (fun j : Fin n => r (p.succAbove j))).comp (dehomCoeff K p) =
      eval₂Hom κ r := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [dehomCoeff, dehomPolynomial]
  · intro i
    rw [RingHom.comp_apply, dehomCoeff_eq_aeval, MvPolynomial.aeval_X]
    cases h : finSuccEquiv' p i with
    | none =>
      have hi : i = p := ((finSuccEquiv'_eq_none).mp h).symm
      subst i
      simp [hr]
    | some j =>
      have hi : i = p.succAbove j := (finSuccEquiv'_eq_some).mp h
      simp [hi]

abbrev chartOpen : (AlgebraicGeometry.Proj (polyGrading K n)).Opens :=
  Proj.basicOpen (polyGrading K n) (X p)

theorem chartOpen_affine : IsAffineOpen (chartOpen (K := K) p) :=
  Proj.isAffineOpen_basicOpen (polyGrading K n) (X p) (X_mem_degree_one K p) Nat.one_pos

/-- The actual section-ring evaluation through the original standard
chart equivalence, with every coefficient retained. -/
def chartEvaluation : Γ(Proj (polyGrading K n), chartOpen (K := K) p) →+* R :=
  (eval₂Hom κ (fun j : Fin n => r (p.succAbove j))).comp
    (sectionsChartEquiv K p).symm.toRingHom

theorem chartEvaluation_sections (F : MvPolynomial (Fin n) K) :
    chartEvaluation κ p r (sectionsChartEquiv K p F) =
      eval₂Hom κ (fun j : Fin n => r (p.succAbove j)) F := by
  simp only [chartEvaluation, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

/-- The actual chart evaluation on every genuine homogeneous fraction. -/
theorem chartEvaluation_fraction (hr : r p = 1) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) K)
    (hF : F ∈ polyGrading K n (d • 1)) :
    chartEvaluation κ p r
      ((Proj.basicOpenIsoAway (polyGrading K n) (X p)
        (X_mem_degree_one K p) Nat.one_pos).hom
          (Away.mk (polyGrading K n) (X_mem_degree_one K p) d F hF)) =
      eval₂Hom κ r F := by
  have h := chartRingEquiv_dehomCoeff K p d F hF
  have hs : (Proj.basicOpenIsoAway (polyGrading K n) (X p)
      (X_mem_degree_one K p) Nat.one_pos).hom
        (Away.mk (polyGrading K n) (X_mem_degree_one K p) d F hF) =
      sectionsChartEquiv K p (dehomCoeff K p F) := by
    rw [sectionsChartEquiv, RingEquiv.trans_apply, h]
    rfl
  rw [hs, chartEvaluation_sections]
  exact RingHom.congr_fun (eval₂_comp_dehomCoeff κ p r hr) F

def awayEvaluation (hr : r p = 1) : Away (polyGrading K n) (X p) →+* R :=
  (Localization.awayLift (eval₂Hom κ r) (X p)
    (by simpa only [MvPolynomial.eval₂Hom_X', hr] using (isUnit_one : IsUnit (1 : R)))).comp
      (algebraMap (Away (polyGrading K n) (X p)) (Localization.Away (X p)))

theorem chartEvaluation_comp_away (hr : r p = 1) :
    (chartEvaluation κ p r).comp
      (Proj.basicOpenIsoAway (polyGrading K n) (X p)
        (X_mem_degree_one K p) Nat.one_pos).hom.hom = awayEvaluation κ p r hr := by
  apply Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext
    (polyGrading K n) (X_mem_degree_one K p)
  intro d F hF
  rw [RingHom.comp_apply, chartEvaluation_fraction κ p r hr]
  exact (NativeProjectiveVectorChart.awayLift_mk (polyGrading K n) (eval₂Hom κ r)
    (X_mem_degree_one K p) (by simpa only [MvPolynomial.eval₂Hom_X'] using hr) d F hF).symm

/-- The actual standard affine chart morphism in the section-ring model. -/
def chartLift : Spec (.of R) ⟶ (chartOpen (K := K) p).toScheme :=
  Spec.map (CommRingCat.ofHom (chartEvaluation κ p r)) ≫ (chartOpen_affine (K := K) p).isoSpec.inv

def chartMap : Spec (.of R) ⟶ AlgebraicGeometry.Proj (polyGrading K n) :=
  chartLift κ p r ≫ (chartOpen (K := K) p).ι

/-- The original affine chart isomorphism acts by its actual section-ring
evaluation on all global sections. -/
theorem chartLift_appTop :
    (chartOpen (K := K) p).topIso.inv ≫ (chartLift κ p r).appTop =
      CommRingCat.ofHom (chartEvaluation κ p r) ≫ (Scheme.ΓSpecIso (.of R)).inv := by
  rw [chartLift, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_inv_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (chartEvaluation κ p r))).symm

theorem chartLift_coordinate (F : MvPolynomial (Fin n) K) :
    (chartLift κ p r).appTop
      ((chartOpen (K := K) p).topIso.inv (sectionsChartEquiv K p F)) =
      (Scheme.ΓSpecIso (.of R)).inv
        (eval₂Hom κ (fun j : Fin n => r (p.succAbove j)) F) := by
  have h := ConcreteCategory.congr_hom (chartLift_appTop κ p r) (sectionsChartEquiv K p F)
  exact h.trans (congrArg (fun x : R => (Scheme.ΓSpecIso (.of R)).inv x)
    (chartEvaluation_sections κ p r F))

/-- The section-ring chart and the genuine degree-zero localization
chart coincide as scheme morphisms, without discarding nilpotents. -/
theorem chartLift_eq_away (hr : r p = 1) :
    chartLift κ p r = Spec.map (CommRingCat.ofHom (awayEvaluation κ p r hr)) ≫
      (Proj.basicOpenIsoSpec (polyGrading K n) (X p)
        (X_mem_degree_one K p) Nat.one_pos).inv := by
  apply (cancel_mono (Proj.basicOpenIsoSpec (polyGrading K n) (X p)
    (X_mem_degree_one K p) Nat.one_pos).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply AlgebraicGeometry.ext_of_isAffine
  have he : (Proj.basicOpenIsoSpec (polyGrading K n) (X p)
      (X_mem_degree_one K p) Nat.one_pos).hom.appTop =
      (Scheme.ΓSpecIso (.of (Away (polyGrading K n) (X p)))).hom ≫
        (Proj.basicOpenIsoAway (polyGrading K n) (X p)
          (X_mem_degree_one K p) Nat.one_pos).hom ≫ (chartOpen (K := K) p).topIso.inv := by
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenIsoAway_hom]
    exact Proj.basicOpenToSpec_app_top (polyGrading K n) (X p)
  rw [Scheme.Hom.comp_appTop, he, Category.assoc, Category.assoc, chartLift_appTop]
  have hc : (Proj.basicOpenIsoAway (polyGrading K n) (X p)
      (X_mem_degree_one K p) Nat.one_pos).hom ≫ CommRingCat.ofHom (chartEvaluation κ p r) =
      CommRingCat.ofHom (awayEvaluation κ p r hr) :=
    CommRingCat.hom_ext (chartEvaluation_comp_away κ p r hr)
  rw [← Category.assoc _ (CommRingCat.ofHom (chartEvaluation κ p r)) _, hc]
  apply (cancel_epi (Scheme.ΓSpecIso (.of (Away (polyGrading K n) (X p)))).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (awayEvaluation κ p r hr))

theorem normalized_span (hr : r p = 1) : Ideal.span (Set.range r) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨p, hr⟩) isUnit_one

/-- The original section-ring standard chart is the actual native Proj
map of the original normalized tuple. -/
theorem chartMap_eq_point (hr : r p = 1) :
    chartMap κ p r = NativeProjectiveVector.point κ r (normalized_span p r hr) := by
  rw [chartMap, chartLift_eq_away κ p r hr, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  exact (NativeProjectiveVectorChart.affine_factor (polyGrading K n) (eval₂Hom κ r)
    (X_mem_degree_one K p) Nat.one_pos (by simpa only [MvPolynomial.eval₂Hom_X'] using hr)
      (NativeProjectiveVector.globalVectorMap_irrelevant κ r (normalized_span p r hr))).symm

/-- The literal homogeneous ring map requested by normalized global
sections, with the canonical Spec structural scalar map. -/
def globalEvaluation : MvPolynomial (Fin (n + 1)) K →+* Γ(Spec (.of R), ⊤) :=
  eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv.hom.comp κ)
    (fun i => (Scheme.ΓSpecIso (.of R)).inv (r i))

theorem globalEvaluation_eq : globalEvaluation κ r = NativeProjectiveVector.globalVectorMap κ r := by
  apply MvPolynomial.ringHom_ext <;> intro a <;>
    simp [globalEvaluation, NativeProjectiveVector.globalVectorMap, NativeProjectiveVector.vectorMap]

theorem globalEvaluation_irrelevant (hr : r p = 1) :
    (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map (globalEvaluation κ r) = ⊤ := by
  rw [globalEvaluation_eq]
  exact NativeProjectiveVector.globalVectorMap_irrelevant κ r (normalized_span p r hr)

theorem chartMap_eq_fromOfGlobalSections (hr : r p = 1) :
    chartMap κ p r = Proj.fromOfGlobalSections (polyGrading K n) (globalEvaluation κ r)
      (globalEvaluation_irrelevant κ p r hr) := by
  rw [chartMap_eq_point κ p r hr]
  exact Proj.fromOfGlobalSections_congr (globalEvaluation_eq κ r).symm _ _

/-- Actual coordinate values uniquely determine a map into the actual
standard affine chart. -/
theorem eq_chartLift_of_coordinates (c : Spec (.of R) ⟶ (chartOpen (K := K) p).toScheme)
    (hc : ∀ F : MvPolynomial (Fin n) K,
      c.appTop ((chartOpen (K := K) p).topIso.inv (sectionsChartEquiv K p F)) =
        (Scheme.ΓSpecIso (.of R)).inv
          (eval₂Hom κ (fun j : Fin n => r (p.succAbove j)) F)) : c = chartLift κ p r := by
  let : IsAffine (chartOpen (K := K) p).toScheme := chartOpen_affine (K := K) p
  apply AlgebraicGeometry.ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso (chartOpen (K := K) p).topIso.inv).surjective s
  obtain ⟨F, rfl⟩ := (sectionsChartEquiv K p).surjective t
  exact (hc F).trans (chartLift_coordinate κ p r F).symm

/-- Coordinate evaluations alone recognize the native projective map;
the conclusion is an actual scheme equality, with no map equality premise. -/
theorem coordinates_eq_fromOfGlobalSections (hr : r p = 1)
    (c : Spec (.of R) ⟶ (chartOpen (K := K) p).toScheme)
    (hc : ∀ F : MvPolynomial (Fin n) K,
      c.appTop ((chartOpen (K := K) p).topIso.inv (sectionsChartEquiv K p F)) =
        (Scheme.ΓSpecIso (.of R)).inv
          (eval₂Hom κ (fun j : Fin n => r (p.succAbove j)) F)) :
    c ≫ (chartOpen (K := K) p).ι =
      Proj.fromOfGlobalSections (polyGrading K n) (globalEvaluation κ r)
        (globalEvaluation_irrelevant κ p r hr) := by
  rw [eq_chartLift_of_coordinates κ p r c hc]
  exact chartMap_eq_fromOfGlobalSections κ p r hr

end M9Native.NativeProjectiveChartEvaluation

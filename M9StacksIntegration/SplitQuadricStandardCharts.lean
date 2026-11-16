module

public import M9StacksIntegration.SplitQuadricLinearSection
public import M9StacksIntegration.SplitQuadricAffineAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceChart
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Clause
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeNonvanishingLocus

/-!
# Genuine standard affine charts of the literal split quadric

The local ideal is computed from the actual zero ideal of the genuine
degree-two section. No saturated homogeneous-ideal equality is assumed.
Its actual polynomial quotient is then identified with affine three-space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheafModule degreeSection)

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.SplitQuadricStandardCharts

open SplitQuadricLinearSection SplitQuadricAffineAlgebra
open Stacks.ProjectiveChart

variable (K : Type u) [Field K]

def chart (c : Fin 4) : (quadric K).Opens :=
  subschemeChart (quadricInclusion K) (pivot c)

theorem chart_isAffineOpen (c : Fin 4) : IsAffineOpen (chart K c) :=
  isAffineOpen_subschemeChart (quadricInclusion K) (pivot c)

/-- The native dehomogenization uses the literal four ordered equations. -/
theorem dehom_equation (c : Fin 4) :
    dehomCoeff K (pivot c) (equation K) = SplitQuadricAffineAlgebra.dehomPolynomial K c := by
  rw [dehomCoeff_eq_aeval]
  fin_cases c <;> simp [equation, pivot, SplitQuadricAffineAlgebra.dehomPolynomial,
    finSuccEquiv', Fin.insertNth, Fin.cons, Fin.succAboveCases, Fin.cases] <;> rfl

/-- Kernel of the actual original closed immersion on each standard open. -/
theorem ker_app_chart (c : Fin 4) :
    RingHom.ker ((quadricInclusion K).app
      (Proj.basicOpen (polyGrading K 4) (X (pivot c)))).hom =
      Ideal.span {sectionsChartEquiv K (pivot c) (dehomCoeff K (pivot c) (equation K))} := by
  have hF : (equation K) ∈ MvPolynomial.homogeneousSubmodule (Fin 5) K (2 • 1) := by
    simpa only [smul_eq_mul, mul_one] using
      (show equation K ∈ polyGrading K 4 2 from (form K).property)
  rw [sectionsChartEquiv_dehomCoeff K (pivot c) 2 _ hF]
  have h := ProjectiveSpectrum.Proj.zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq
    (polyGrading K 4) (X_mem_degree_one K (pivot c)) Nat.one_pos 2 (by simp) (form K) hF
  have hk : (quadricInclusion K).ker =
      zeroScheme (Proj (polyGrading K 4)) (twistingSheafModule (polyGrading K 4) (2 : ℤ))
        (degreeSection (polyGrading K 4) 2 (form K)) :=
    (Scheme.IdealSheafData.ker_subschemeι (quadricIdeal K)).trans (quadricIdeal_eq K)
  let U : (ambient K).affineOpens :=
    ⟨Proj.basicOpen (polyGrading K 4) (X (pivot c)), isAffineOpen_basicOpen_X (R := K) (pivot c)⟩
  have hki := congrArg (fun J : (ambient K).IdealSheafData => J.ideal U) hk
  simpa only [U, SplitQuadricLinearSection.form, polyGrading, Scheme.Hom.ker_apply] using hki.trans h

/-- The actual chart ring has the explicit dehomogeneous quadratic kernel. -/
theorem ker_chartPresentation (c : Fin 4) :
    RingHom.ker (chartPresentation (quadricInclusion K) (pivot c)) = chartIdeal K c := by
  have h := ker_chartPresentation_of_ker_app (quadricInclusion K) (pivot c)
    (dehomCoeff K (pivot c) (equation K)) (ker_app_chart K c)
  simpa only [dehom_equation, chartIdeal] using h

def quotientChartEquiv (c : Fin 4) :
    (PolynomialFour K ⧸ chartIdeal K c) ≃+* Γ(quadric K, chart K c) :=
  (Ideal.quotEquivOfEq (ker_chartPresentation K c).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (chartPresentation_surjective (quadricInclusion K) (pivot c)))

theorem quotientChartEquiv_mk (c : Fin 4) (p : PolynomialFour K) :
    quotientChartEquiv K c (Ideal.Quotient.mk (chartIdeal K c) p) =
      chartPresentation (quadricInclusion K) (pivot c) p := by
  simp only [quotientChartEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

/-- The ring isomorphism is constructed from the genuine chart presentation. -/
def chartRingEquiv (c : Fin 4) : Γ(quadric K, chart K c) ≃+* PolynomialThree K :=
  (quotientChartEquiv K c).symm.trans (chartEquiv K c).toRingEquiv

/-- Every actual chart coordinate has its literal affine polynomial value. -/
theorem chartRingEquiv_presentation (c : Fin 4) (p : PolynomialFour K) :
    chartRingEquiv K c (chartPresentation (quadricInclusion K) (pivot c) p) =
      chartMap K c p := by
  rw [← quotientChartEquiv_mk K c p]
  exact (congrArg (chartEquiv K c)
    ((quotientChartEquiv K c).symm_apply_apply _)).trans (chartEquiv_mk K c p)

/-- The actual standard open of the actual split quadric is an actual
affine-three scheme, including its entire scheme structure. -/
def chartIsoAffineThree (c : Fin 4) :
    (chart K c).toScheme ≅ Spec (.of (PolynomialThree K)) :=
  (chart_isAffineOpen K c).isoSpec ≪≫
    (Scheme.Spec.mapIso (chartRingEquiv K c).toCommRingCatIso.op).symm

def affineThreeMap (c : Fin 4) : Spec (.of (PolynomialThree K)) ⟶ quadric K :=
  (chartIsoAffineThree K c).inv ≫ (chart K c).ι

theorem affineThreeMap_isOpenImmersion (c : Fin 4) : IsOpenImmersion (affineThreeMap K c) := by
  dsimp [affineThreeMap]
  infer_instance

/-- Every actual point of the original section-zero scheme contains the
actual quadratic equation in its homogeneous prime ideal. -/
theorem equation_mem (x : quadric K) :
    equation K ∈ (quadricInclusion K x).asHomogeneousIdeal := by
  let p := quadricInclusion K x
  by_contra hF
  have hb : p ∈ Proj.basicOpen (polyGrading K 4) (equation K) := hF
  have hi : p ∈ Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible (polyGrading K 4) 1 := by
    rw [Stacks.AlgebraicGeometry.ProjTwistPowers.whereInvertible_one_eq_top _
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin 5) K)]
    trivial
  have hn := (Stacks.AlgebraicGeometry.ProjTwistPowers.mem_nonvanishingLocus_degreeSection_iff_of_eq
    (polyGrading K 4) (k := 2) (d := 2) (by simp) (form K) hi).mpr hb
  have hnot := (AlgebraicGeometry.mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme
    (twistingSheafModule (polyGrading K 4) (2 : ℤ))
    (degreeSection (polyGrading K 4) 2 (form K)) p).mp hn
  have hs : p ∈ (quadricIdeal K).supportSet := by
    have hr := congrArg (fun S : Set (ambient K) => p ∈ S)
      (Scheme.IdealSheafData.range_subschemeι (quadricIdeal K))
    exact hr.mp (show p ∈ Set.range (quadricInclusion K) from ⟨x, rfl⟩)
  apply hnot
  rw [quadricIdeal_eq K] at hs
  exact hs

/-- The four genuine standard opens cover the entire actual quadric. -/
theorem charts_cover (x : quadric K) : ∃ c : Fin 4, x ∈ chart K c := by
  classical
  by_contra! h
  let p := quadricInclusion K x
  let I := p.asHomogeneousIdeal.toIdeal
  have h0 : X (0 : Fin 5) ∈ I := by
    simpa [I, p, chart, subschemeChart, pivot, Proj.mem_basicOpen] using h 2
  have h2 : X (2 : Fin 5) ∈ I := by
    simpa [I, p, chart, subschemeChart, pivot, Proj.mem_basicOpen] using h 1
  have h3 : X (3 : Fin 5) ∈ I := by
    simpa [I, p, chart, subschemeChart, pivot, Proj.mem_basicOpen] using h 0
  have h4 : X (4 : Fin 5) ∈ I := by
    simpa [I, p, chart, subschemeChart, pivot, Proj.mem_basicOpen] using h 3
  have hq : equation K ∈ I := equation_mem K x
  have h02 : X (0 : Fin 5) * X 2 ∈ I := I.mul_mem_right _ h0
  have h34 : X (3 : Fin 5) * X 4 ∈ I := I.mul_mem_right _ h3
  have hs : (X (1 : Fin 5))^2 ∈ I := by
    have ht := I.sub_mem h02 (I.add_mem hq h34)
    convert ht using 1 <;> simp only [equation] <;> ring
  have h1 : X (1 : Fin 5) ∈ I := p.isPrime.mem_of_pow_mem 2 hs
  have hp : p ∈ ⨆ i : Fin 5, Proj.basicOpen (polyGrading K 4) (X i) := by
    rw [iSup_basicOpen_X_eq_top K 4]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  change X i ∉ I at hi
  fin_cases i
  · exact hi h0
  · exact hi h1
  · exact hi h2
  · exact hi h3
  · exact hi h4

theorem affineThreeMaps_cover (x : quadric K) :
    ∃ c : Fin 4, x ∈ Set.range (affineThreeMap K c) := by
  obtain ⟨c, hc⟩ := charts_cover K x
  let y : (chart K c).toScheme := ⟨x, hc⟩
  refine ⟨c, (chartIsoAffineThree K c).hom y, ?_⟩
  change (chart K c).ι ((chartIsoAffineThree K c).inv ((chartIsoAffineThree K c).hom y)) = x
  have he : (chartIsoAffineThree K c).inv ((chartIsoAffineThree K c).hom y) = y := by
    change ((chartIsoAffineThree K c).hom ≫ (chartIsoAffineThree K c).inv) y = y
    rw [Iso.hom_inv_id]
    rfl
  exact (congrArg (chart K c).ι he).trans rfl

/-- An actual open cover by the four constructed affine-three schemes. -/
def affineThreeCover : (quadric K).OpenCover := by
  letI (c : Fin 4) := affineThreeMap_isOpenImmersion K c
  exact Scheme.Cover.mkOfCovers (Fin 4)
    (fun _ => Spec (.of (PolynomialThree K))) (affineThreeMap K)
    (fun x => by
      obtain ⟨c, y, hy⟩ := affineThreeMaps_cover K x
      exact ⟨c, y, hy⟩)

end M9Native.SplitQuadricStandardCharts

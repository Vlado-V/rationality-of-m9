module

public import M9StacksIntegration.HomogeneousEquationIdeal
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceChart

/-! Genuine affine presentations of finite homogeneous zero schemes.
On every native coordinate chart the actual closed-immersion kernel is
the ideal of the literal dehomogenized equations, retaining nilpotents. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveChart

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.HomogeneousEquationChart

variable (K : Type u) [CommRing K] (n d : ℕ)
    {ι : Type v} [Finite ι] (F : ι → polyGrading K n d)

def ideal : (AlgebraicGeometry.Proj (polyGrading K n)).IdealSheafData :=
  ⨆ i, HomogeneousEquationIdeal.equationIdeal K n d F i

def inclusion : (ideal K n d F).subscheme ⟶ AlgebraicGeometry.Proj (polyGrading K n) :=
  (ideal K n d F).subschemeι

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion K n d F) :=
  inferInstanceAs (IsClosedImmersion (ideal K n d F).subschemeι)

def chartIdeal (p : Fin (n+1)) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range fun i => dehomCoeff K p (F i))

/-- The actual ambient-chart kernel, in the original native section ring. -/
theorem ker_app_chart (p : Fin (n+1)) :
    RingHom.ker ((inclusion K n d F).app
      (Proj.basicOpen (polyGrading K n) (MvPolynomial.X p))).hom =
      Ideal.span (Set.range fun i => sectionsChartEquiv K p (dehomCoeff K p (F i))) := by
  let U : (AlgebraicGeometry.Proj (polyGrading K n)).affineOpens :=
    ⟨Proj.basicOpen (polyGrading K n) (MvPolynomial.X p), isAffineOpen_basicOpen_X p⟩
  have hk : (inclusion K n d F).ker = homogeneousIdealSheaf (polyGrading K n)
      (HomogeneousEquationIdeal.homogeneousSpan K n d F) :=
    (Scheme.IdealSheafData.ker_subschemeι (ideal K n d F)).trans
      (HomogeneousEquationIdeal.homogeneousIdealSheaf_eq_iSup_equationIdeal K n d F).symm
  have hki := congrArg (fun I : (AlgebraicGeometry.Proj (polyGrading K n)).IdealSheafData => I.ideal U) hk
  have hkip : RingHom.ker ((inclusion K n d F).app
      (Proj.basicOpen (polyGrading K n) (MvPolynomial.X p))).hom =
      (homogeneousIdealSheaf (polyGrading K n)
        (HomogeneousEquationIdeal.homogeneousSpan K n d F)).ideal U := by
    simpa only [U, Scheme.Hom.ker_apply] using hki
  rw [hkip]
  rw [homogeneousIdealSheaf_ideal_basicOpen_eq_span_range _ _ (X_mem_degree_one K p)
    Nat.one_pos (fun i => (F i : MvPolynomial (Fin (n+1)) K)) (fun _ => d)
    (fun i => by simpa only [smul_eq_mul, mul_one] using (F i).property)
    (HomogeneousEquationIdeal.homogeneousSpan_toIdeal K n d F)]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact (sectionsChartEquiv_dehomCoeff K p d (F i)
    (by simpa only [smul_eq_mul, mul_one] using (F i).property)).symm

/-- The literal polynomial presentation has exactly the dehomogeneous
equation ideal as its kernel; this is an equality of actual ideals. -/
theorem ker_chartPresentation (p : Fin (n+1)) :
    RingHom.ker (chartPresentation (inclusion K n d F) p) = chartIdeal K n d F p := by
  change (RingHom.ker ((inclusion K n d F).app
      (Proj.basicOpen (polyGrading K n) (MvPolynomial.X p))).hom).comap
        (sectionsChartEquiv K p).toRingHom = _
  rw [ker_app_chart]
  have hm : Ideal.span (Set.range fun i => sectionsChartEquiv K p (dehomCoeff K p (F i))) =
      (chartIdeal K n d F p).map (sectionsChartEquiv K p).toRingHom := by
    rw [chartIdeal, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hm]
  exact Ideal.comap_map_of_bijective _ (sectionsChartEquiv K p).bijective

/-- The full native closed-scheme chart is the polynomial quotient by
the original dehomogenized equations. -/
def chartQuotientEquiv (p : Fin (n+1)) :
    (MvPolynomial (Fin n) K ⧸ chartIdeal K n d F p) ≃+*
      Γ((ideal K n d F).subscheme, subschemeChart (inclusion K n d F) p) :=
  (Ideal.quotEquivOfEq (ker_chartPresentation K n d F p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (chartPresentation_surjective (inclusion K n d F) p))

end M9Native.HomogeneousEquationChart

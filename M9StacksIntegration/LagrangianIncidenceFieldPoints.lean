module

public import M9StacksIntegration.LagrangianFieldCoordinates
public import M9StacksIntegration.LagrangianLinearSectionLineCharts
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! Actual rational-point lifts of the original universal LG incidence.
Both the five-dimensional quotient and the determinant coordinate vector
are obtained from the original native chart triangles. Projective
intersection supplies a closed LG point; the literal tensor-section
equations then factor it through the original family zero scheme. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianFieldCoordinates
open M9Native.LagrangianLinearSections M9Native.LagrangianLinearSectionEquations
open M9Native.LagrangianLinearSectionLineCharts
open AlgebraicGeometry.Grassmannian

universe u

namespace M9Native.LagrangianIncidenceFieldPoints

variable (K : Type u) [Field K]

/-- Every actual field point of the native quotient scheme factors through
one of its original normalized affine charts. -/
theorem exists_integralChart_factor {k n : ℕ}
    (p : Spec (.of K) ⟶ AlgebraicGeometry.Grassmannian.scheme.{u} k n) :
    ∃ (ι : Fin (n - k) ↪ Fin n)
      (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
        (ChartIndex.{u} (k := k) (n := n) ι) (ULift.{u} ℤ)))),
      p = g ≫ chart k n ι := by
  obtain ⟨ι, hι⟩ := exists_mem_range_chart k n (p (IsLocalRing.closedPoint K))
  have hrange : Set.range p ⊆ Set.range (chart k n ι) := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst a
    exact hι
  exact ⟨ι, IsOpenImmersion.lift (chart k n ι) p hrange,
    (IsOpenImmersion.lift_fac _ _ hrange).symm⟩

def parameterChartMatrix (ι : Fin 5 ↪ Fin 14)
    (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (ChartIndex.{u} (k := 9) (n := 14) ι) (ULift.{u} ℤ)))) :
    Matrix (Fin 5) (Fin 14) K :=
  (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι g)).map
    (Scheme.ΓSpecIso (.of K)).hom.hom

theorem parameterChartMatrix_pivots (ι : Fin 5 ↪ Fin 14)
    (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (ChartIndex.{u} (k := 9) (n := 14) ι) (ULift.{u} ℤ)))) :
    (parameterChartMatrix K ι g).submatrix id ι = 1 := by
  ext i j
  change (Scheme.ΓSpecIso (.of K)).hom.hom
    (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ι g) i (ι j)) =
      if i = j then 1 else 0
  rw [toMatrix_chartQuotientMap, chartMatrix_apply_self (k := 9) (n := 14)]
  split_ifs <;> simp

/-- Full quotient rank follows from the actual identity pivot columns. -/
theorem parameterChartMatrix_surjective (ι : Fin 5 ↪ Fin 14)
    (g : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (ChartIndex.{u} (k := 9) (n := 14) ι) (ULift.{u} ℤ)))) :
    Function.Surjective (parameterChartMatrix K ι g).mulVec := by
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mpr
  apply le_antisymm (Matrix.rank_le_card_height _)
  have h := Matrix.rank_submatrix_le (parameterChartMatrix K ι g) id ι
  rwa [parameterChartMatrix_pivots K ι g, Matrix.rank_one] at h

variable [CharZero K] [IsAlgClosed K]

/-- Every original K-valued parameter point has an actual K-valued point
in the original incidence family. No fibre, rank, or coefficient premise
is supplied. -/
theorem exists_familyPoint_of_parameterPoint
    (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _) :
    ∃ z : Spec (.of K) ⟶ family K, z ≫ familyProjection K = p := by
  obtain ⟨ιP, gP, hP⟩ := exists_integralChart_factor K
    (p ≫ GrassmannianCharts.toIntegral K 9 14)
  let A := parameterChartMatrix K ιP gP
  have hA : Function.Surjective A.mulVec := parameterChartMatrix_surjective K ιP gP
  obtain ⟨x, hxc, hx⟩ := exists_closed_lagrangian_point_in_linearSection K A.mulVecLin hA
  let : IsProper (LagrangianGrassmannian.projection K) :=
    isProper_of_isProjectiveMorphism _
      (LagrangianPluckerClosed.isProjectiveMorphism_projection K)
  let l := pointOfClosedPoint (LagrangianGrassmannian.projection K) x hxc
  have hl : l ≫ LagrangianGrassmannian.projection K = 𝟙 _ :=
    pointOfClosedPoint_comp _ _ _
  obtain ⟨ιL, gL, hL⟩ := exists_integralChart_factor K
    ((l ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _)
  have hmem : LagrangianPlucker.primitivePlucker K (l (IsLocalRing.closedPoint K)) ∈
      linearSection K A.mulVecLin := by simpa only [l, pointOfClosedPoint_apply] using hx
  have hcoeff := (lagrangianPoint_mem_linearSection_iff K l hl ιL gL hL
    A.mulVecLin (IsLocalRing.closedPoint K)).mp hmem
  let f : Spec (.of K) ⟶ LagrangianLinearSections.ambient K :=
    pullback.lift l p (hl.trans hp.symm)
  have hfL : f ≫ toLG K = l := pullback.lift_fst _ _ _
  have hfP : f ≫ toParameter K = p := pullback.lift_snd _ _ _
  have hLf : ((f ≫ toLG K) ≫ LagrangianGrassmannian.inclusion K) ≫ pullback.snd _ _ =
      gL ≫ chart 3 6 ιL := by rw [hfL]; exact hL
  have hPf : (f ≫ toParameter K) ≫ GrassmannianCharts.toIntegral K 9 14 =
      gP ≫ chart 9 14 ιP := by rw [hfP]; exact hP
  obtain ⟨d, hd⟩ := LagrangianLinearSectionQuotientCharts.pullback_ambient_chart_isomorphic
    K f ιP gP hPf
  have hzero : (Stacks.FreeSheafMatrix.toMatrix (chartQuotientMap 9 14 ιP gP)).mulVec
      (lineCoefficients K f (ambientLineIso K f ιL gL hLf)) = 0 := by
    rw [ambientLineIso_coefficients]
    apply (matrix_equation_iff K _ _).mpr
    change A.mulVec (values K (LagrangianPlucker.chartCoordinates K (f ≫ toLG K) ιL gL)) = 0
    rw [hfL]
    exact hcoeff
  obtain ⟨z, hz⟩ := (factorsThrough_iff_matrix_zero K f
    (ambientLineIso K f ιL gL hLf) d (chartQuotientMap 9 14 ιP gP) hd).mpr hzero
  refine ⟨z, ?_⟩
  rw [familyProjection, ← Category.assoc, hz]
  exact hfP

end M9Native.LagrangianIncidenceFieldPoints

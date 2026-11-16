module

public import M9StacksIntegration.GrassmannianCharts
public import M9StacksIntegration.MukaiOrderedMinors

/-!
# Actual normalized matrices for native Grassmannian K-points

Every K-point of the native rank-two quotient Grassmannian is lifted
through an actual chart open immersion. Its actual chart functions give a
normalized two-row matrix over K; the resulting native matrix point is
proved equal to the original morphism of schemes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiGrassmannianPoints

variable (K : Type u) [Field K]

abbrev grass := GrassmannianCharts.space K 3 5

def matrixPoint (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K) :
    Spec (.of K) ⟶ grass K :=
  pullback.lift (𝟙 _)
    (GrassmannianCharts.matrixPoint K 3 5 ι M ≫ Grassmannian.chart 3 5 ι)
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem matrixPoint_projection
    (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K) :
    matrixPoint K ι M ≫ GrassmannianCharts.projection K 3 5 = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem matrixPoint_toIntegral
    (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K) :
    matrixPoint K ι M ≫ GrassmannianCharts.toIntegral K 3 5 =
      GrassmannianCharts.matrixPoint K 3 5 ι M ≫ Grassmannian.chart 3 5 ι :=
  pullback.lift_snd _ _ _

/-- Evaluate the native integral chart functions using the actual
global-section isomorphism of Spec K. -/
def fieldChartMatrix (ι : MukaiOrderedMinors.OrderedPair)
    (h : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) (ULift.{u} ℤ)))) :
    Matrix (Fin 2) (Fin 5) K :=
  (Grassmannian.chartMatrix (k := 3) (n := 5) ι
    (AffineSpace.toSpecMvPolyIntEquiv
      (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) h)).map
    (Scheme.ΓSpecIso (.of K)).hom.hom

theorem fieldChartMatrix_pivots (ι : MukaiOrderedMinors.OrderedPair)
    (h : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) (ULift.{u} ℤ)))) :
    (fieldChartMatrix K ι h).submatrix id ι = 1 := by
  ext i j
  simp only [fieldChartMatrix,Matrix.submatrix_apply,Matrix.map_apply,id_eq,Matrix.one_apply]
  rw [Grassmannian.chartMatrix_apply_self (k := 3) (n := 5)]
  split_ifs <;> simp

theorem matrixPoint_fieldChartMatrix (ι : MukaiOrderedMinors.OrderedPair)
    (h : Spec (.of K) ⟶ Spec (.of (MvPolynomial
      (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) (ULift.{u} ℤ)))) :
    GrassmannianCharts.matrixPoint K 3 5 ι (fieldChartMatrix K ι h) = h := by
  apply (AffineSpace.toSpecMvPolyIntEquiv _).injective
  funext a
  rcases a with ⟨⟨⟨j,hj⟩,i⟩⟩
  simp only [GrassmannianCharts.matrixPoint,Equiv.apply_symm_apply,fieldChartMatrix,
    Matrix.map_apply,Grassmannian.chartMatrix_apply_of_notMem _ _ _ hj]
  exact (Scheme.ΓSpecIso (.of K)).hom_inv_id_apply _

/-- Every actual K-valued quotient point has a normalized genuine matrix
representative. The equality is of original scheme morphisms. -/
theorem exists_matrixPoint (p : Spec (.of K) ⟶ grass K)
    (hp : p ≫ GrassmannianCharts.projection K 3 5 = 𝟙 _) :
    ∃ (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K),
      M.submatrix id ι = 1 ∧ matrixPoint K ι M = p := by
  let a₀ := IsLocalRing.closedPoint K
  obtain ⟨ι,y,hy⟩ := GrassmannianCharts.charts_cover K 3 5 (p a₀)
  have hrange : Set.range p ⊆ Set.range (GrassmannianCharts.chartOver K 3 5 ι) := by
    rintro _ ⟨a,rfl⟩
    have ha : a = a₀ := Subsingleton.elim _ _
    subst a
    exact ⟨y,hy⟩
  let g := IsOpenImmersion.lift (GrassmannianCharts.chartOver K 3 5 ι) p hrange
  have hg : g ≫ GrassmannianCharts.chartOver K 3 5 ι = p :=
    IsOpenImmersion.lift_fac _ _ hrange
  let h := g ≫ AffineSpace.toSpecMvPoly
    (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) (Spec (.of K))
  refine ⟨ι,fieldChartMatrix K ι h,fieldChartMatrix_pivots K ι h,?_⟩
  apply pullback.hom_ext
  · exact (matrixPoint_projection K ι _).trans hp.symm
  · rw [matrixPoint_toIntegral,matrixPoint_fieldChartMatrix]
    calc
      h ≫ Grassmannian.chart 3 5 ι =
          g ≫ (GrassmannianCharts.chartOver K 3 5 ι ≫
            GrassmannianCharts.toIntegral K 3 5) := by
        rw [GrassmannianCharts.chartOver_toIntegral]
        rfl
      _ = p ≫ GrassmannianCharts.toIntegral K 3 5 := by rw [← Category.assoc,hg]

end M9Native.MukaiGrassmannianPoints

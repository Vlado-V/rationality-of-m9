module

public import M9StacksIntegration.GrassmannianFieldKernels
public import M9StacksIntegration.GrassmannianChartClass
public import M9StacksIntegration.MatrixKernelChartNormalization

/-! Actual chart ring coordinates and normalized matrices of field-valued points of the
native Grassmannian. The chart lift is obtained from the genuine open cover. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

namespace M9Native.GrassmannianFieldChartCoordinates

open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix SplitMatrixGrassmannian

variable {B K : Type} [Field B] [Field K] [Algebra B K]
variable (r n : ℕ) (ι : Fin (n-r) ↪ Fin n)

abbrev Polynomial := GrassmannianCharts.chartPolynomial B r n ι

def matrix (φ : Polynomial (B := B) r n ι →ₐ[B] K) : Matrix (Fin (n-r)) (Fin n) K :=
  chartMatrix ι (fun a => φ (MvPolynomial.X a))

theorem matrix_pivots (φ : Polynomial (B := B) r n ι →ₐ[B] K) :
    (matrix r n ι φ).submatrix id ι = 1 := by
  ext i j
  change chartMatrix ι (fun a => φ (MvPolynomial.X a)) i (ι j) =
    (1 : Matrix (Fin (n-r)) (Fin (n-r)) K) i j
  rw [chartMatrix_apply_self]
  rfl

theorem matrix_surjective (φ : Polynomial (B := B) r n ι →ₐ[B] K) :
    Function.Surjective (matrix r n ι φ).mulVec := by
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨MatrixKernelChartNormalization.pivotSection ι,?_⟩
  rw [MatrixKernelChartNormalization.mul_section,matrix_pivots]

theorem matrix_entriesIn (E : Subfield K) (φ : Polynomial (B := B) r n ι →ₐ[B] K)
    (hφ : ∀ a, φ (MvPolynomial.X a) ∈ E) :
    MatrixChartFieldRecovery.EntriesIn E (matrix r n ι φ) := by
  classical
  intro i j
  by_cases hj : j ∈ Set.range ι
  · obtain ⟨j',rfl⟩ := hj
    change chartMatrix ι (fun a => φ (MvPolynomial.X a)) i (ι j') ∈ E
    rw [chartMatrix_apply_self]
    split_ifs
    · exact E.one_mem
    · exact E.zero_mem
  · change chartMatrix ι (fun a => φ (MvPolynomial.X a)) i j ∈ E
    rw [chartMatrix_apply_of_notMem ι _ i hj]
    exact hφ _

def point (φ : Polynomial (B := B) r n ι →ₐ[B] K) :
    Spec (.of K) ⟶ GrassmannianCharts.space B r n :=
  Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ GrassmannianCharts.chartSpecMap B r n ι

@[reassoc] theorem point_projection (φ : Polynomial (B := B) r n ι →ₐ[B] K) :
    point r n ι φ ≫ GrassmannianCharts.projection B r n =
      Spec.map (CommRingCat.ofHom (algebraMap B K)) := by
  rw [point,Category.assoc,GrassmannianCharts.chartSpecMap_projection,← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext φ.comp_algebraMap

def integralPoint (φ : Polynomial (B := B) r n ι →ₐ[B] K) :
    Spec (.of K) ⟶ coordinateChartScheme.{0} ι :=
  Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (AffineSpace.SpecIso (ChartIndex.{0} ι) (.of B)).inv ≫
      AffineSpace.toSpecMvPoly (ChartIndex.{0} ι) (Spec (.of B))

theorem integralPoint_coordinates (φ : Polynomial (B := B) r n ι →ₐ[B] K) (a : ChartIndex.{0} ι) :
    AffineSpace.toSpecMvPolyIntEquiv _ (integralPoint r n ι φ) a =
      (Scheme.ΓSpecIso (.of K)).inv (φ (MvPolynomial.X a)) := by
  rw [integralPoint,AffineSpace.toSpecMvPolyIntEquiv_comp,
    AffineSpace.toSpecMvPolyIntEquiv_comp]
  change (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop
    ((AffineSpace.SpecIso (ChartIndex.{0} ι) (.of B)).inv.appTop
      (AffineSpace.coord (Spec (.of B)) a)) = _
  rw [AffineSpace.SpecIso_inv_appTop_coord,← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality,CommRingCat.comp_apply]
  rfl

theorem point_toIntegral (φ : Polynomial (B := B) r n ι →ₐ[B] K) :
    point r n ι φ ≫ GrassmannianCharts.toIntegral B r n = integralPoint r n ι φ ≫ chart r n ι := by
  rw [point,Category.assoc,GrassmannianCharts.chartSpecMap,
    Category.assoc,GrassmannianCharts.chartOver_toIntegral]
  simp only [integralPoint,Category.assoc]
  rfl

theorem point_class (φ : Polynomial (B := B) r n ι →ₐ[B] K) :
    (functorData r n).objEquiv (Spec (.of K)) ((schemeRepresentableBy r n).homEquiv
      (point r n ι φ ≫ GrassmannianCharts.toIntegral B r n)) =
      ⟦fieldPresentation r n K (matrix r n ι φ) (matrix_surjective r n ι φ)⟧ := by
  rw [point_toIntegral,GrassmannianChartClass.chart_class]
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨Iso.refl _,?_⟩
  change (GrassmannianChartClass.normalized r n ι (integralPoint r n ι φ)).val ≫ 𝟙 _ = _
  rw [Category.comp_id,GrassmannianChartClass.normalized_map]
  apply toMatrix_injective
  rw [toMatrix_chartQuotientMap,fieldPresentation_matrix]
  rw [show AffineSpace.toSpecMvPolyIntEquiv _ (integralPoint r n ι φ) =
    fun a => (Scheme.ΓSpecIso (.of K)).inv (φ (MvPolynomial.X a)) by
      funext a; exact integralPoint_coordinates r n ι φ a]
  exact chartMatrix_map ι (Scheme.ΓSpecIso (.of K)).inv.hom _

/-- Every actual field-valued point lifts through an actual polynomial chart,
with the original base-field scalars retained. -/
theorem exists_coordinates (q : Spec (.of K) ⟶ GrassmannianCharts.space B r n)
    (hq : q ≫ GrassmannianCharts.projection B r n =
      Spec.map (CommRingCat.ofHom (algebraMap B K))) :
    ∃ (ι : Fin (n-r) ↪ Fin n) (φ : Polynomial (B := B) r n ι →ₐ[B] K), point r n ι φ = q := by
  let a₀ := IsLocalRing.closedPoint K
  obtain ⟨ι,y,hy⟩ := GrassmannianCharts.charts_cover B r n (q a₀)
  have hrange : Set.range q ⊆ Set.range (GrassmannianCharts.chartOver B r n ι) := by
    rintro _ ⟨a,rfl⟩
    have ha : a = a₀ := Subsingleton.elim _ _
    subst a
    exact ⟨y,hy⟩
  let g := IsOpenImmersion.lift (GrassmannianCharts.chartOver B r n ι) q hrange
  have hg : g ≫ GrassmannianCharts.chartOver B r n ι = q :=
    IsOpenImmersion.lift_fac _ _ hrange
  let h := g ≫ (AffineSpace.SpecIso (ChartIndex.{0} ι) (.of B)).hom
  have hfac : h ≫ GrassmannianCharts.chartSpecMap B r n ι = q := by
    simp only [h,GrassmannianCharts.chartSpecMap,Category.assoc,Iso.hom_inv_id_assoc,hg]
  let f := Spec.preimage h
  have hf : (CommRingCat.ofHom (MvPolynomial.C (σ := ChartIndex.{0} ι))) ≫ f =
      CommRingCat.ofHom (algebraMap B K) := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_preimage,← GrassmannianCharts.chartSpecMap_projection,
      ← Category.assoc,hfac,hq]
  let φ : Polynomial (B := B) r n ι →ₐ[B] K :=
    { toRingHom := f.hom
      commutes' c := congrArg (fun a : CommRingCat.of B ⟶ CommRingCat.of K => a c) hf }
  refine ⟨ι,φ,?_⟩
  change Spec.map f ≫ _ = q
  rw [Spec.map_preimage]
  exact hfac

end M9Native.GrassmannianFieldChartCoordinates

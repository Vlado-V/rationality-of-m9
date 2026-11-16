module

public import M9StacksIntegration.PrimitiveRhoFiberNondegenerate
public import M9StacksIntegration.GrassmannianFieldChartCoordinates
public import M9StacksIntegration.SplitMatrixGrassmannianNaturality

/-! Actual native Gr4 graph points of the original nondegenerate rho-fiber
domain, with their literal matrix kernels over every extension field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Module
open scoped Classical Matrix

namespace M9Native.PrimitiveRhoGraphNativePoints
open M9.GraphBundleDescent
open PrimitiveRhoFiberChart PrimitiveRhoFiberNondegenerate

variable (K : Type) [Field K] [Algebra ℂ K]

def graphRingPoint (f : nondegenerateRing →ₐ[ℂ] K) : parameterRing →ₐ[ℂ] K :=
  f.comp localizationMap

def baseAt (f : nondegenerateRing →ₐ[ℂ] K) (s : Fin 2) : BaseMatrix K :=
  (universalBaseLocalized (K := ℂ) s).map (graphRingPoint K f).toRingHom

def isomAt (f : nondegenerateRing →ₐ[ℂ] K) : Matrix.GeneralLinearGroup (Fin 4) K :=
  Matrix.GeneralLinearGroup.map (graphRingPoint K f).toRingHom (universalIsomorphism (K := ℂ))

def chartCoordinates (f : nondegenerateRing →ₐ[ℂ] K) :
    GraphGrassmannianChart.nativePolynomial ℂ →ₐ[ℂ] K :=
  (graphRingPoint K f).comp (GraphGrassmannianChart.nativePolynomialToGraph ℂ)

/-- This is the original nondegenerate graph inclusion into the actual native Grassmannian. -/
def point (f : nondegenerateRing →ₐ[ℂ] K) :
    Spec (.of K) ⟶ GrassmannianCharts.space ℂ 4 12 :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ inclusion ≫ GraphGrassmannianChart.graphMap ℂ

theorem point_eq_chart (f : nondegenerateRing →ₐ[ℂ] K) :
    point K f = GrassmannianFieldChartCoordinates.point 4 12
      GraphGrassmannianChart.pivot (chartCoordinates K f) := by
  rw [point,inclusion,GraphGrassmannianChart.graphMap_eq,
    GrassmannianFieldChartCoordinates.point]
  simp only [← Category.assoc,← Spec.map_comp,← CommRingCat.ofHom_comp]
  rfl

@[reassoc] theorem point_projection (f : nondegenerateRing →ₐ[ℂ] K) :
    point K f ≫ GrassmannianCharts.projection ℂ 4 12 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ K)) := by
  rw [point_eq_chart]
  exact GrassmannianFieldChartCoordinates.point_projection 4 12 _ _

def quotient (f : nondegenerateRing →ₐ[ℂ] K) : Matrix (Fin 8) (Fin 12) K :=
  GrassmannianFieldChartCoordinates.matrix 4 12 GraphGrassmannianChart.pivot (chartCoordinates K f)

theorem quotient_surjective (f : nondegenerateRing →ₐ[ℂ] K) :
    Function.Surjective (quotient K f).mulVec :=
  GrassmannianFieldChartCoordinates.matrix_surjective 4 12 _ _

theorem quotient_eq_kernelMatrix (f : nondegenerateRing →ₐ[ℂ] K) :
    quotient K f = GraphGrassmannianChart.kernelMatrix
      (GraphGrassmannianChart.blockRows (baseAt K f 0) (isomAt K f).val
        (baseAt K f 1 * (isomAt K f).val)) := by
  rw [quotient,GrassmannianFieldChartCoordinates.matrix,
    GraphGrassmannianChart.kernelMatrix_eq_chartMatrix]
  congr 1
  funext a
  change graphRingPoint K f
    (GraphGrassmannianChart.nativePolynomialToGraph ℂ (MvPolynomial.X a)) = _
  rw [GraphGrassmannianChart.nativePolynomialToGraph,MvPolynomial.aeval_X,map_neg]
  have h := GraphGrassmannianChart.blockRows_map (graphRingPoint K f).toRingHom
    (universalBaseLocalized (K := ℂ) 0) (universalFiberLocalized (K := ℂ))
    (universalBaseLocalized (K := ℂ) 1 * universalFiberLocalized (K := ℂ))
  rw [Matrix.map_mul] at h
  exact congrArg Neg.neg (congrFun (congrFun h
    (GraphGrassmannianChart.coordinateIndexEquiv a).1)
      (GraphGrassmannianChart.coordinateIndexEquiv a).2)

theorem localizedGraph_map (f : nondegenerateRing →ₐ[ℂ] K) :
    localizedGraph.map f = graphMatrix K (baseAt K f 0) (baseAt K f 1) (isomAt K f) := by
  change parameterGraph.map (graphRingPoint K f).toRingHom = _
  rw [parameterGraph,graphMatrix_map]
  rfl

/-- The native represented quotient has exactly the original graph-column range as kernel. -/
theorem quotient_kernel (f : nondegenerateRing →ₐ[ℂ] K) :
    (Matrix.toLin' (quotient K f)).ker = (Matrix.toLin' (localizedGraph.map f)).range := by
  rw [quotient_eq_kernelMatrix,GraphGrassmannianChart.kernel_eq_actualGraph,
    localizedGraph_map,graphMatrix,Matrix.toLin'_toMatrix']

/-- The actual native point class is this genuine split field-matrix quotient. -/
theorem point_class (f : nondegenerateRing →ₐ[ℂ] K) :
    SplitMatrixGrassmannianNaturality.pointClass 4 12 ℂ (point K f) =
      ⟦SplitMatrixGrassmannian.fieldPresentation 4 12 K (quotient K f) (quotient_surjective K f)⟧ := by
  rw [point_eq_chart]
  exact GrassmannianFieldChartCoordinates.point_class 4 12 _ _

/-- Native graph-point equality is exactly equality of the original literal graph subspaces. -/
theorem points_eq_iff_graph_ranges_eq (f g : nondegenerateRing →ₐ[ℂ] K) :
    point K f = point K g ↔
      (Matrix.toLin' (localizedGraph.map f)).range =
        (Matrix.toLin' (localizedGraph.map g)).range := by
  have hb : point K f ≫ GrassmannianCharts.projection ℂ 4 12 =
      point K g ≫ GrassmannianCharts.projection ℂ 4 12 := by
    rw [point_projection,point_projection]
  rw [GrassmannianFieldKernels.points_eq_iff_kernel_eq (K := K) (k := 4) (n := 12)
    (point K f) (point K g) (quotient K f) (quotient K g)
    (quotient_surjective K f) (quotient_surjective K g) (point_class K f) (point_class K g) hb]
  change (Matrix.toLin' (quotient K f)).ker = (Matrix.toLin' (quotient K g)).ker ↔ _
  rw [quotient_kernel,quotient_kernel]

end M9Native.PrimitiveRhoGraphNativePoints

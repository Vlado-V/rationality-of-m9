module

public import M9StacksIntegration.PrimitiveRadicalOrbitGenericPoints
public import M9StacksIntegration.PrimitiveRhoGraphNativePoints

@[expose] public section

/-! The genuine native reduced Grassmannian field inside the actual orbit-family
source field, with its actual generic points and geometric equalizer. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Module
open scoped Classical Matrix TensorProduct

namespace M9Native.PrimitiveRadicalSliceField
open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitRings PrimitiveRadicalOrbitPoints
open PrimitiveRadicalOrbitKernelPoints PrimitiveRadicalOrbitGenericPoints
open PrimitiveRhoFiberReducedCoordinates PrimitiveRhoFiberNondegenerate
open NativeGenericPullbackEvaluation
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveRadicalFiber
open M9.PrimitiveBlockCoordinates

/-- The original graph inclusion, restricted to its actual nondegenerate open. -/
def reducedMap : nondegenerateDomain ⟶ GrassmannianCharts.space ℂ 4 12 :=
  inclusion ≫ GraphGrassmannianChart.graphMap ℂ

@[reassoc] theorem reducedMap_projection :
    reducedMap ≫ GrassmannianCharts.projection ℂ 4 12 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ nondegenerateRing)) := by
  rw [reducedMap,Category.assoc,GraphGrassmannianChart.graphMap_projection,
    GraphGrassmannianChart.domainProjection]
  have h := PrimitiveRhoFiberNondegenerate.map_projection
  rw [PrimitiveRhoFiberNondegenerate.map,Category.assoc,PrimitiveRhoFiberChart.map_projection] at h
  exact h

/-- This is a genuine morphism from the original tensor source to the original
native reduced Grassmannian, rather than a chosen rational-field identification. -/
def sliceMap : source ⟶ GrassmannianCharts.space ℂ 4 12 := fiberProjection ≫ reducedMap

@[reassoc] theorem sliceMap_projection :
    sliceMap ≫ GrassmannianCharts.projection ℂ 4 12 = projection := by
  rw [sliceMap,Category.assoc,reducedMap_projection,fiberProjection_over]

instance sliceMap_isDominant : IsDominant sliceMap := by
  have : IsDominant fiberProjection := by
    unfold fiberProjection
    apply NativeDominantFunctionField.specMap_isDominant
    exact Algebra.TensorProduct.includeRight_injective
      (A := gaussRing) (B := fiberRing) (algebraMap ℂ gaussRing).injective
  have : IsDominant inclusion := ⟨inclusion_dense⟩
  have : IsDominant (GraphGrassmannianChart.graphMap ℂ) :=
    ⟨GraphGrassmannianChart.graphMap_dense ℂ⟩
  unfold sliceMap reducedMap
  infer_instance

/-- The actual reduced native generic stalk embeds by the actual fiber projection. -/
def sliceEmbedding : (GrassmannianCharts.space ℂ 4 12).functionField →ₐ[ℂ]
    source.functionField where
  toRingHom := NativeDominantFunctionField.map sliceMap
  commutes' c := by
    have h := NativeDominantFunctionField.map_scalar ℂ sliceMap
      (GrassmannianCharts.projection ℂ 4 12)
    rw [sliceMap_projection] at h
    exact DFunLike.congr_fun h c

theorem sliceEmbedding_injective : Function.Injective sliceEmbedding := sliceEmbedding.injective

variable (K : Type) [Field K] [Algebra ℂ K]

theorem nativeSlicePoint_eq (y : Point K) :
    Spec.map (CommRingCat.ofHom y.toRingHom) ≫ sliceMap =
      PrimitiveRhoGraphNativePoints.point K (rightPoint K y) := by
  rw [sliceMap,reducedMap,PrimitiveRhoGraphNativePoints.point,fiberProjection]
  simp only [← Category.assoc,← Spec.map_comp,← CommRingCat.ofHom_comp]
  rfl

/-- Every source-field embedding gives exactly the genuine reduced generic
field point determined by the actual slice-field embedding. -/
theorem slicePoint_sourcePoint (s : source.functionField →ₐ[ℂ] K) :
    PrimitiveRhoGraphNativePoints.point K (rightPoint K (sourcePoint K s)) =
      point (X := GrassmannianCharts.space ℂ 4 12) (s.comp sliceEmbedding).toRingHom := by
  rw [← nativeSlicePoint_eq,sourcePoint_spec]
  exact NativeGenericPointNaturality.point_comp_dominant sliceMap s.toRingHom

local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

theorem rhoFieldPoints_eq_of_graph_ranges_eq (f g : nondegenerateRing →ₐ[ℂ] K)
    (h : (Matrix.toLin' (localizedGraph.map f)).range =
      (Matrix.toLin' (localizedGraph.map g)).range) :
    PrimitiveRadicalKernelPair.fieldPoint K f = PrimitiveRadicalKernelPair.fieldPoint K g := by
  apply (rhoFiberEquiv K).injective
  apply Subtype.ext
  apply Submodule.map_injective_of_injective
    (f := (reducedCoordinates K).toLinearMap) (reducedCoordinates K).injective
  rw [rhoFiberEquiv_fieldPoint_coordinates,rhoFiberEquiv_fieldPoint_coordinates,h]

/-- Agreement on the true native reduced function field forces equality of
the actual intrinsic rho-fiber points. -/
theorem rhoFieldPoints_eq_of_slice_embeddings_eq (s t : source.functionField →ₐ[ℂ] K)
    (h : s.comp sliceEmbedding = t.comp sliceEmbedding) :
    PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K (sourcePoint K s)) =
      PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K (sourcePoint K t)) := by
  have hp : PrimitiveRhoGraphNativePoints.point K (rightPoint K (sourcePoint K s)) =
      PrimitiveRhoGraphNativePoints.point K (rightPoint K (sourcePoint K t)) := by
    rw [slicePoint_sourcePoint,slicePoint_sourcePoint,h]
  exact rhoFieldPoints_eq_of_graph_ranges_eq K _ _
    ((PrimitiveRhoGraphNativePoints.points_eq_iff_graph_ranges_eq K _ _).mp hp)

/-- The actual native-slice field kernel pair is related by an actual original
symplectic transformation of the original primitive nine-planes. -/
theorem planeAt_relation_of_slice_embeddings_eq (s t : source.functionField →ₐ[ℂ] K)
    (h : s.comp sliceEmbedding = t.comp sliceEmbedding) :
    planeAt K (sourcePoint K t) =
      planeAction K (originalGroupAt K (sourcePoint K t) * (originalGroupAt K (sourcePoint K s))⁻¹)
        (planeAt K (sourcePoint K s)) := by
  have hρ := rhoFieldPoints_eq_of_slice_embeddings_eq K s t h
  change planeAction K (originalGroupAt K (sourcePoint K t)) _ =
    planeAction K (originalGroupAt K (sourcePoint K t) * (originalGroupAt K (sourcePoint K s))⁻¹)
      (planeAction K (originalGroupAt K (sourcePoint K s)) _)
  rw [← PrimitiveRadicalKernelPair.planeAction_mul,mul_assoc,inv_mul_cancel,mul_one,hρ]

end M9Native.PrimitiveRadicalSliceField

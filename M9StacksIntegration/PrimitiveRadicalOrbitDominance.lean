module

public import M9StacksIntegration.PrimitiveRadicalOrbitFieldRecovery
public import M9StacksIntegration.GeneratedCoordinateIndependence
public import M9StacksIntegration.NativeDominantFunctionField

/-! Dominance of the actual thirteen-plus-thirty-two parameter orbit family in the
native Grassmannian. It follows from actual radical and graph parameter recovery. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory

namespace M9Native.PrimitiveRadicalOrbitDominance

open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitRings PrimitiveRadicalOrbitPoints
open PrimitiveRadicalOrbitParameterRecovery PrimitiveRadicalOrbitFieldRecovery

theorem sourceField_trdeg : Algebra.trdeg ℂ L = 45 := by
  rw [sourceRationalFin45Equiv.trdeg_eq]
  have : Algebra.IsAlgebraic (MvPolynomial (Fin 45) ℂ)
      (FractionRing (MvPolynomial (Fin 45) ℂ)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin 45) ℂ))
  have h := trdeg_add_eq ℂ (MvPolynomial (Fin 45) ℂ)
    (A := FractionRing (MvPolynomial (Fin 45) ℂ))
  rw [trdeg_eq_zero (R := MvPolynomial (Fin 45) ℂ),add_zero] at h
  rw [← h]
  simp [MvPolynomial.trdeg_of_isDomain]

theorem chartCoordinates_algebraicIndependent (ι : Fin 5 ↪ Fin 14)
    (φ : GrassmannianFieldChartCoordinates.Polynomial (B := ℂ) 9 14 ι →ₐ[ℂ] L)
    (hpoint : GrassmannianFieldChartCoordinates.point 9 14 ι φ = nativePoint L genericPoint) :
    AlgebraicIndependent ℂ (fun a => φ (MvPolynomial.X a)) := by
  apply GeneratedCoordinateIndependence.algebraicIndependent_of_recovery _
    (source_isAlgebraic ι φ hpoint)
  have hc : Fintype.card (AlgebraicGeometry.Grassmannian.ChartIndex (k := 9) (n := 14) ι) = 45 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (GrassmannianCharts.chartIndexEquiv 9 14 ι)
  rw [sourceField_trdeg,hc]
  norm_num

theorem chartCoordinateHom_injective (ι : Fin 5 ↪ Fin 14)
    (φ : GrassmannianFieldChartCoordinates.Polynomial (B := ℂ) 9 14 ι →ₐ[ℂ] L)
    (hpoint : GrassmannianFieldChartCoordinates.point 9 14 ι φ = nativePoint L genericPoint) :
    Function.Injective φ := by
  have he : MvPolynomial.aeval (fun a => φ (MvPolynomial.X a)) = φ := by
    apply MvPolynomial.algHom_ext
    intro a
    exact MvPolynomial.aeval_X _ _
  have h := chartCoordinates_algebraicIndependent ι φ hpoint
  change Function.Injective (MvPolynomial.aeval (fun a => φ (MvPolynomial.X a))) at h
  rwa [he] at h

/-- The literal generic-source-field point is dominant, because the forty-five actual
coordinates of its native target chart are algebraically independent. -/
theorem nativeGenericPoint_isDominant : IsDominant (nativePoint L genericPoint) := by
  obtain ⟨ι,φ,hpoint⟩ := GrassmannianFieldChartCoordinates.exists_coordinates 9 14
    (nativePoint L genericPoint) (nativePoint_projection L genericPoint)
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    NativeDominantFunctionField.specMap_isDominant _ (chartCoordinateHom_injective ι φ hpoint)
  haveI : IsDominant (GrassmannianCharts.chartSpecMap ℂ 9 14 ι) :=
    ⟨GrassmannianCharts.chartSpecMap_dense ℂ 9 14 ι⟩
  rw [← hpoint,GrassmannianFieldChartCoordinates.point]
  infer_instance

/-- Genuine dominance of the original native orbit family, using the actual fibre recovery. -/
instance map_isDominant : IsDominant PrimitiveRadicalOrbitFamily.map := by
  haveI : IsDominant
      (Spec.map (CommRingCat.ofHom genericPoint.toRingHom) ≫ PrimitiveRadicalOrbitFamily.map) :=
    nativeGenericPoint_isDominant
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom genericPoint.toRingHom))
    PrimitiveRadicalOrbitFamily.map

theorem map_dense : DenseRange PrimitiveRadicalOrbitFamily.map :=
  PrimitiveRadicalOrbitFamily.map.denseRange

/-- The induced injection uses the genuine generic stalks of the original native schemes. -/
def functionFieldEmbedding : (GrassmannianCharts.space ℂ 9 14).functionField →ₐ[ℂ]
    PrimitiveRadicalOrbitFamily.source.functionField where
  toRingHom := NativeDominantFunctionField.map PrimitiveRadicalOrbitFamily.map
  commutes' c := by
    have h := NativeDominantFunctionField.map_scalar ℂ PrimitiveRadicalOrbitFamily.map
      (GrassmannianCharts.projection ℂ 9 14)
    rw [PrimitiveRadicalOrbitFamily.map_projection] at h
    exact congrArg (fun f : ℂ →+* PrimitiveRadicalOrbitFamily.source.functionField => f c) h

theorem functionFieldEmbedding_injective : Function.Injective functionFieldEmbedding :=
  functionFieldEmbedding.injective

end M9Native.PrimitiveRadicalOrbitDominance

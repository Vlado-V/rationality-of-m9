module

public import M9StacksIntegration.LagrangianGrassmannian
public import M9StacksIntegration.GrassmannianCharts
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.Topology.Dimension.OpenCover

/-! Actual dimension nine of the original ambient native Gr(3,6),
proved from its genuine affine-nine open charts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.LagrangianDegree

variable (K : Type u) [Field K]

theorem ambient_chartSpec_dimension (i : Fin 3 ↪ Fin 6) :
    topologicalKrullDim (Spec (.of
      (MvPolynomial (Grassmannian.ChartIndex.{u} (k := 3) (n := 6) i) K))) =
        (9 : WithBot ℕ∞) := by
  have hcard : Nat.card (Grassmannian.ChartIndex.{u} (k := 3) (n := 6) i) = 9 := by
    simpa only [Nat.card_fin] using Nat.card_congr (GrassmannianCharts.chartIndexEquiv 3 6 i)
  change topologicalKrullDim
    (PrimeSpectrum (MvPolynomial (Grassmannian.ChartIndex.{u} (k := 3) (n := 6) i) K)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, hcard,
    ringKrullDim_eq_zero_of_field K]
  norm_num

theorem ambient_chart_dimension (i : Fin 3 ↪ Fin 6) :
    topologicalKrullDim (GrassmannianCharts.chartSpace K 3 6 i) =
      (9 : WithBot ℕ∞) := by
  let e := AffineSpace.SpecIso (Grassmannian.ChartIndex.{u} (k := 3) (n := 6) i) (.of K)
  apply le_antisymm
  · have h := e.hom.isOpenEmbedding.isInducing.topologicalKrullDim_le
    rw [ambient_chartSpec_dimension K i] at h
    exact h
  · have h := e.inv.isOpenEmbedding.isInducing.topologicalKrullDim_le
    rw [ambient_chartSpec_dimension K i] at h
    exact h

theorem ambient_dimension :
    topologicalKrullDim (M9Native.LagrangianGrassmannian.grassmannian K) =
      (9 : WithBot ℕ∞) := by
  apply le_antisymm
  · exact topologicalKrullDim_le_of_isOpen_cover
      (fun i : Fin 3 ↪ Fin 6 => Set.range (GrassmannianCharts.chartOver K 3 6 i))
      (fun i => (GrassmannianCharts.chartOver K 3 6 i).isOpenEmbedding.isOpen_range)
      (GrassmannianCharts.charts_cover K 3 6)
      (fun i => by
        let h := (GrassmannianCharts.chartOver K 3 6 i).isOpenEmbedding.isEmbedding.toHomeomorph
        have hd : topologicalKrullDim (Set.range (GrassmannianCharts.chartOver K 3 6 i)) =
            (9 : WithBot ℕ∞) := by
          rw [← IsHomeomorph.topologicalKrullDim_eq h h.isHomeomorph,
            ambient_chart_dimension K i]
        exact hd.le)
  · let i := GrassmannianCharts.standardEmbedding 3 6
    have h := (GrassmannianCharts.chartSpecMap K 3 6 i).isOpenEmbedding.isInducing.topologicalKrullDim_le
    rw [ambient_chartSpec_dimension K i] at h
    exact h

end M9Native.LagrangianDegree

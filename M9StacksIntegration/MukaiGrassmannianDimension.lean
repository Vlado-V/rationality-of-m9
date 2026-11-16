module

public import M9StacksIntegration.GrassmannianCharts
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# A genuine affine-six chart in the native Grassmannian

This is the lower dimension bound needed by the five-section
Castelnuovo argument. The chart is the actual native open immersion from
the spectrum of its six-variable coordinate ring. No dimension formula
for an independently modeled Grassmannian is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.MukaiGrassmannianDimension

variable (K : Type u) [Field K]

theorem chartSpec_dimension (ι : Fin 2 ↪ Fin 5) :
    topologicalKrullDim (Spec (.of (MvPolynomial (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) K))) =
      (6 : WithBot ℕ∞) := by
  have hcard : Nat.card (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) = 6 := by
    simpa only [Nat.card_fin] using
      Nat.card_congr (GrassmannianCharts.chartIndexEquiv 3 5 ι)
  change topologicalKrullDim
    (PrimeSpectrum (MvPolynomial (Grassmannian.ChartIndex.{u} (k := 3) (n := 5) ι) K)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,hcard,
    ringKrullDim_eq_zero_of_field K]
  norm_num

/-- The six-dimensional native affine chart gives the required lower
bound for the actual representing Grassmannian over K. -/
theorem grass_dimension_lower :
    (6 : WithBot ℕ∞) ≤ topologicalKrullDim (GrassmannianCharts.space K 3 5) := by
  let ι := GrassmannianCharts.standardEmbedding 3 5
  have h := (GrassmannianCharts.chartSpecMap K 3 5 ι).isOpenEmbedding.isInducing.topologicalKrullDim_le
  rw [chartSpec_dimension K ι] at h
  exact h

end M9Native.MukaiGrassmannianDimension

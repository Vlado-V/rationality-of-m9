module

public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace

/-!
# Actual local dimensions of finite formal power-series models

The native regular-local theorem and the explicit native cotangent basis
compute both the Krull dimension and the cotangent dimension. This is an
algebraic adapter for a genuinely constructed versal power-series model;
it neither constructs a curve deformation model nor assumes its dimension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

universe u v

namespace M9Native.PowerSeriesLocalDimension

variable (k : Type u) [Field k]

/-- The actual power-series ring has its actual number of variables as dimension. -/
theorem powerSeries_krullDimension (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) k) = (n : WithBot ℕ∞) := by
  let := isRegularLocalRing_mvPowerSeries k n
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (MvPowerSeries (Fin n) k)).mp (inferInstance : IsRegularLocalRing _)
  rw [Stacks.MvPowerSeries.RegularParameters.finrank_cotangentSpace_field] at h
  exact h.symm

variable {k} {R : Type v} [CommRing R] [Algebra k R]

/-- An actual algebra isomorphism to a power-series ring derives regularity. -/
theorem regularLocal_of_powerSeriesEquiv {n : ℕ}
    (e : R ≃ₐ[k] MvPowerSeries (Fin n) k) : IsRegularLocalRing R := by
  let := isRegularLocalRing_mvPowerSeries k n
  exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv

/-- The dimension is transported from the actual ring, not supplied as an input. -/
theorem krullDimension_of_powerSeriesEquiv {n : ℕ}
    (e : R ≃ₐ[k] MvPowerSeries (Fin n) k) : ringKrullDim R = (n : WithBot ℕ∞) :=
  (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).trans (powerSeries_krullDimension k n)

/-- The same actual model computes the original cotangent-space rank. -/
theorem cotangent_finrank_of_powerSeriesEquiv {n : ℕ}
    (e : R ≃ₐ[k] MvPowerSeries (Fin n) k) :
    letI := regularLocal_of_powerSeriesEquiv e
    Module.finrank (ResidueField R) (CotangentSpace R) = n := by
  let := regularLocal_of_powerSeriesEquiv e
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
    (inferInstance : IsRegularLocalRing R)
  rw [krullDimension_of_powerSeriesEquiv e] at h
  exact_mod_cast h

/-- Two genuinely constructed power-series models have the same variable count. -/
theorem powerSeries_variable_count_unique {n m : ℕ}
    (e : R ≃ₐ[k] MvPowerSeries (Fin n) k)
    (e' : R ≃ₐ[k] MvPowerSeries (Fin m) k) : n = m := by
  have h : (n : WithBot ℕ∞) = m :=
    (krullDimension_of_powerSeriesEquiv e).symm.trans
      (krullDimension_of_powerSeriesEquiv e')
  exact_mod_cast h

end M9Native.PowerSeriesLocalDimension

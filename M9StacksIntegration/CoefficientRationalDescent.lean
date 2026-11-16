module

public import M9.FiniteNoNameField
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Rational-function coefficient descent for arbitrary groups

The polynomial and fraction-field actions and the inclusion are exactly
those of `FiniteNoNameField`. No finiteness of the group is needed: a
reduced denominator is unique up to a scalar, and fixing one nonzero
coefficient to one gives a genuinely invariant polynomial denominator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace M9Native.CoefficientRationalDescent

open M9.FiniteNoNameField

variable (G L : Type*) [Group G] [Field L] [MulSemiringAction G L] (ι : Type*)

theorem polynomialAction_C (g : G) (c : L) :
    g • (MvPolynomial.C c : PolynomialRing L ι) = MvPolynomial.C (g • c) := by
  rw [polynomialAction_apply, MvPolynomial.map_C]
  rfl

/-- Coprimality makes a reduced denominator divide each of its translates. -/
theorem denominator_dvd_translate (p q : PolynomialRing L ι) (hpq : IsRelPrime p q)
    (hq : q ≠ 0)
    (hf : ∀ g : G, g • (algebraMap _ (RationalField L ι) p /
      algebraMap _ (RationalField L ι) q) = algebraMap _ (RationalField L ι) p /
        algebraMap _ (RationalField L ι) q) (g : G) : q ∣ g • q := by
  let j := algebraMap (PolynomialRing L ι) (RationalField L ι)
  have hj : Function.Injective j := IsFractionRing.injective _ _
  have hgq : g • q ≠ 0 := by
    simpa only [smul_zero] using (MulAction.injective g).ne hq
  have hjq : j q ≠ 0 := fun h => hq (hj (h.trans (map_zero j).symm))
  have hjgq : j (g • q) ≠ 0 := fun h => hgq (hj (h.trans (map_zero j).symm))
  have he := hf g
  simp only [smul_div₀', rationalAction_polynomial] at he
  have hc : (g • p) * q = p * (g • q) := by
    apply hj
    simpa only [map_mul] using (div_eq_div_iff hjgq hjq).mp he
  apply hpq.symm.dvd_of_dvd_mul_left
  rw [← hc]
  exact dvd_mul_left q (g • p)

/-- Applying the same divisibility to the inverse group element gives actual associates. -/
theorem denominator_associated_translate (p q : PolynomialRing L ι) (hpq : IsRelPrime p q)
    (hq : q ≠ 0)
    (hf : ∀ g : G, g • (algebraMap _ (RationalField L ι) p /
      algebraMap _ (RationalField L ι) q) = algebraMap _ (RationalField L ι) p /
        algebraMap _ (RationalField L ι) q) (g : G) : Associated q (g • q) := by
  have h₁ := denominator_dvd_translate G L ι p q hpq hq hf g
  obtain ⟨r,hr⟩ := denominator_dvd_translate G L ι p q hpq hq hf g⁻¹
  have h₂ : g • q ∣ q := by
    refine ⟨g • r, ?_⟩
    have h := congrArg (fun x : PolynomialRing L ι => g • x) hr
    simpa only [smul_inv_smul, smul_mul'] using h
  exact associated_of_dvd_dvd h₁ h₂

/-- The only units of the polynomial ring over a field are nonzero constant polynomials. -/
theorem denominator_translate_scalar (p q : PolynomialRing L ι) (hpq : IsRelPrime p q)
    (hq : q ≠ 0)
    (hf : ∀ g : G, g • (algebraMap _ (RationalField L ι) p /
      algebraMap _ (RationalField L ι) q) = algebraMap _ (RationalField L ι) p /
        algebraMap _ (RationalField L ι) q) (g : G) :
    ∃ c : L, c ≠ 0 ∧ g • q = MvPolynomial.C c * q := by
  obtain ⟨u,hu⟩ := denominator_associated_translate G L ι p q hpq hq hf g
  obtain ⟨c,hc,huc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  refine ⟨c,hc.ne_zero,?_⟩
  rw [← hu,huc,mul_comm]

/-- Normalization by one coefficient removes the scalar ambiguity for every group element. -/
theorem normalized_denominator_fixed (p q : PolynomialRing L ι) (hpq : IsRelPrime p q)
    (hq : q ≠ 0)
    (hf : ∀ g : G, g • (algebraMap _ (RationalField L ι) p /
      algebraMap _ (RationalField L ι) q) = algebraMap _ (RationalField L ι) p /
        algebraMap _ (RationalField L ι) q) (α : ι →₀ ℕ) :
    ∀ g : G, g • (MvPolynomial.C ((q.coeff α)⁻¹) * q) =
      MvPolynomial.C ((q.coeff α)⁻¹) * q := by
  intro g
  obtain ⟨c,hc,hgq⟩ := denominator_translate_scalar G L ι p q hpq hq hf g
  have hcoeff : g • q.coeff α = c * q.coeff α := by
    have h := congrArg (fun a : PolynomialRing L ι => a.coeff α) hgq
    simpa only [polynomialAction_coeff, MvPolynomial.coeff_C_mul] using h
  calc
    g • (MvPolynomial.C ((q.coeff α)⁻¹) * q) =
        MvPolynomial.C ((g • q.coeff α)⁻¹) * (g • q) := by
      rw [smul_mul', polynomialAction_C, smul_inv₀']
    _ = MvPolynomial.C ((c * q.coeff α)⁻¹) * (MvPolynomial.C c * q) := by rw [hcoeff,hgq]
    _ = MvPolynomial.C ((q.coeff α)⁻¹) * q := by
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      congr 1
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- Fixed rational functions in fixed independent variables descend to the actual coefficient
fixed field, for arbitrary groups and arbitrary sets of variables. -/
theorem fixed_rational_iff_descends (f : RationalField L ι) :
    (∀ g : G, g • f = f) ↔
      ∃ h : FractionRing (MvPolynomial ι (FixedField G L)), rationalInclude G L ι h = f := by
  classical
  constructor
  · intro hf
    obtain ⟨p,⟨q,hq⟩,hpq,hrep⟩ := IsFractionRing.exists_reduced_fraction (PolynomialRing L ι) f
    let j := algebraMap (PolynomialRing L ι) (RationalField L ι)
    have hj : Function.Injective j := IsFractionRing.injective _ _
    have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
    have hjq : j q ≠ 0 := fun h => hq0 (hj (h.trans (map_zero j).symm))
    have hr : j p / j q = f := by simpa only [IsFractionRing.mk'_eq_div] using hrep
    have hfix : ∀ g : G, g • (j p / j q) = j p / j q := by
      intro g
      simpa only [hr] using hf g
    obtain ⟨α,hα⟩ := MvPolynomial.exists_coeff_ne_zero hq0
    let c : PolynomialRing L ι := MvPolynomial.C ((q.coeff α)⁻¹)
    let d := c * q
    let n := c * p
    have hc : c ≠ 0 := MvPolynomial.C_ne_zero.mpr (inv_ne_zero hα)
    have hd : d ≠ 0 := mul_ne_zero hc hq0
    have hjd : j d ≠ 0 := fun h => hd (hj (h.trans (map_zero j).symm))
    have hdf : ∀ g : G, g • d = d := normalized_denominator_fixed G L ι p q hpq hq0 hfix α
    have hn : j n = f * j d := by
      calc
        j n = j c * j p := map_mul j c p
        _ = j c * ((j p / j q) * j q) := by rw [div_mul_cancel₀ _ hjq]
        _ = (j p / j q) * (j c * j q) := by ring
        _ = f * j d := by rw [hr,← map_mul]
    have hnf : ∀ g : G, g • n = n := by
      intro g
      apply hj
      rw [← rationalAction_polynomial,hn,smul_mul',hf g,rationalAction_polynomial,hdf g]
    obtain ⟨num,hnum⟩ := fixed_polynomial_descends G L ι n hnf
    obtain ⟨den,hden⟩ := fixed_polynomial_descends G L ι d hdf
    refine ⟨algebraMap _ (FractionRing (MvPolynomial ι (FixedField G L))) num /
      algebraMap _ (FractionRing (MvPolynomial ι (FixedField G L))) den,?_⟩
    rw [map_div₀,rationalInclude_polynomial,rationalInclude_polynomial,hnum,hden]
    exact (div_eq_iff hjd).mpr hn
  · rintro ⟨h,rfl⟩ g
    exact rationalInclude_fixed G L ι h g

/-- The equality is for the literal range of the original fraction-field inclusion. -/
theorem rationalInclude_fieldRange :
    (rationalInclude G L ι).fieldRange = FixedRationalField G L ι := by
  ext f
  exact (fixed_rational_iff_descends G L ι f).symm

def fixedRationalEquiv : FractionRing (MvPolynomial ι (FixedField G L)) ≃+*
    FixedRationalField G L ι :=
  (rationalInclude G L ι).rangeRestrictFieldEquiv.trans
    (RingEquiv.subfieldCongr (rationalInclude_fieldRange G L ι))

/-- The actual coefficient fixed field is the constant field of the resulting rational field. -/
def fixedRationalAlgEquiv : FractionRing (MvPolynomial ι (FixedField G L)) ≃ₐ[FixedField G L]
    FixedRationalField G L ι where
  __ := fixedRationalEquiv G L ι
  commutes' a := by
    apply Subtype.ext
    exact rationalInclude_constant G L ι a

@[simp] theorem fixedRationalAlgEquiv_apply
    (f : FractionRing (MvPolynomial ι (FixedField G L))) :
    (fixedRationalAlgEquiv G L ι f : RationalField L ι) = rationalInclude G L ι f := rfl

@[simp] theorem fixedRationalAlgEquiv_constant (a : FixedField G L) :
    (fixedRationalAlgEquiv G L ι (algebraMap (FixedField G L)
      (FractionRing (MvPolynomial ι (FixedField G L))) a) : RationalField L ι) =
      algebraMap L (RationalField L ι) (a : L) := by
  rw [fixedRationalAlgEquiv_apply,rationalInclude_constant]

end M9Native.CoefficientRationalDescent

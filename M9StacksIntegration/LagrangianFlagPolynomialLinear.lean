module

public import M9StacksIntegration.LagrangianFlagCoefficientFunctional
public import M9StacksIntegration.LagrangianPolynomialLineCongruence

/-!
# Additivity of the actual free-six flag integral

The map below is a composite of genuine Chow coefficient evaluation,
the native change of grade, and the three original proper pushforwards.
The independent coefficient functional is only an additive map; no
geometric formula is a premise of these definitions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow MvPolynomial
universe u
namespace M9Native.LagrangianFlagPolynomialLinear
open LagrangianFlagCoefficientFunctional LagrangianFlagPowerStages LagrangianChowPolynomials

abbrev Polynomial3 := MvPolynomial (Fin 3) ℤ

theorem exponent_eq_iff (a b c d e f : ℕ) :
    exponent a b c = exponent d e f ↔ a=d ∧ b=e ∧ c=f := by
  constructor
  · intro h
    have h0 := congrArg (fun v : Fin 3 →₀ ℕ => v 0) h
    have h1 := congrArg (fun v : Fin 3 →₀ ℕ => v 1) h
    have h2 := congrArg (fun v : Fin 3 →₀ ℕ => v 2) h
    exact ⟨by simpa [exponent] using h0,
      by simpa [exponent] using h1, by simpa [exponent] using h2⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

theorem exponent_coordinates (d : Fin 3 →₀ ℕ) : exponent (d 0) (d 1) (d 2) = d := by
  ext i
  fin_cases i <;> simp [exponent]

theorem monomial_exponent_one (a b c : ℕ) :
    monomial (exponent a b c) (1:ℤ) = X 0^a * X 1^b * X 2^c := by
  simp [exponent, MvPolynomial.X, monomial_pow, monomial_mul_monomial]

theorem monomial_eq_zsmul (d : Fin 3 →₀ ℕ) (r : ℤ) :
    monomial d r = r • monomial d (1:ℤ) := by
  simp [MvPolynomial.smul_monomial]

/-- The six coefficients, with the actual positive quotient-root signs. -/
def functionalHom : Polynomial3 →+ ℤ :=
  coeffAddMonoidHom (exponent 5 4 3) - coeffAddMonoidHom (exponent 4 5 3) -
    coeffAddMonoidHom (exponent 5 3 4) + coeffAddMonoidHom (exponent 3 5 4) +
    coeffAddMonoidHom (exponent 4 3 5) - coeffAddMonoidHom (exponent 3 4 5)

theorem functionalHom_apply (p : Polynomial3) : functionalHom p = functional p := rfl

theorem functional_monomial_one (a b c : ℕ) :
    functional (monomial (exponent a b c) (1:ℤ)) =
      (if a=5 ∧ b=4 ∧ c=3 then 1 else 0) -
      (if a=4 ∧ b=5 ∧ c=3 then 1 else 0) -
      (if a=5 ∧ b=3 ∧ c=4 then 1 else 0) +
      (if a=3 ∧ b=5 ∧ c=4 then 1 else 0) +
      (if a=4 ∧ b=3 ∧ c=5 then 1 else 0) -
      (if a=3 ∧ b=4 ∧ c=5 then 1 else 0) := by
  simp only [functional, coeff_monomial, exponent_eq_iff]

theorem functional_monomial_one_of_ne_twelve (a b c : ℕ) (h : a+b+c≠12) :
    functional (monomial (exponent a b c) (1:ℤ)) = 0 := by
  rw [functional_monomial_one]
  split_ifs <;> omega

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1LFT LagrangianFlagPowerStages.projection2LFT
  LagrangianFlagPowerStages.projection3LFT

variable {T : Scheme.{u}} (E : T.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (C : ChowSituation.{u}) (q : T ⟶ C.S) [LocallyOfFiniteType q]

/-- Actual coefficient-twelve evaluation and actual three proper pushes. -/
def integralMap (k : ℤ) (α : chowGroup C q k) : Polynomial3 →+ chowGroup C q k :=
  (triplePush E C q k).comp
    ((chowGroupCast C (baseMap3 E C q) (by omega : (k+12)-(12:ℤ)=k)).toAddMonoidHom.comp
      (applyComponent C (baseMap3 E C q) (positiveLines E) (k+12) 12
        (flatPullClass E C q k α)))

theorem triplePush_heq {a b : ℤ} (hab : a=b)
    {x : chowGroup C (baseMap3 E C q) a}
    {y : chowGroup C (baseMap3 E C q) b} (hxy : x ≍ y) :
    triplePush E C q a x ≍ triplePush E C q b y := by
  cases hab
  cases hxy
  rfl

theorem integralMap_apply_heq (k : ℤ) (α : chowGroup C q k) (p : Polynomial3) :
    integralMap E C q k α p ≍
      triplePush E C q ((k+12)-(12:ℤ))
        (evaluate C (baseMap3 E C q) (positiveLines E) p (k+12) 12
          (flatPullClass E C q k α)) := by
  exact triplePush_heq E C q (by omega)
    (chowGroupCast_heq C (baseMap3 E C q) (by omega : (k+12)-(12:ℤ)=k)
      (evaluate C (baseMap3 E C q) (positiveLines E) p (k+12) 12
        (flatPullClass E C q k α)))

/-- The coefficient functional acting on the SAME original Chow class. -/
def functionalClassMap (k : ℤ) (α : chowGroup C q k) : Polynomial3 →+ chowGroup C q k where
  toFun p := functionalHom p • α
  map_zero' := by simp
  map_add' p r := by simp only [map_add, add_zsmul]

/-- The same literal integral evaluated in the original three named flag lines. -/
theorem integralMap_eq_original (k : ℤ) (α : chowGroup C q k) (p : Polynomial3) :
    integralMap E C q k α p = triplePush E C q k
      (chowGroupCast C (baseMap3 E C q) (by omega)
        (evaluate C (baseMap3 E C q)
          (LagrangianPolynomialLineCongruence.originalLines E) p
          (k+12) 12 (flatPullClass E C q k α))) := by
  exact congrArg (fun f : Polynomial3 →+* GradedCapFamily (chowGroup C (baseMap3 E C q)) =>
    triplePush E C q k
      (chowGroupCast C (baseMap3 E C q) (by omega : (k+12)-(12:ℤ)=k)
        (f p (k+12) 12 (flatPullClass E C q k α))))
    (LagrangianPolynomialLineCongruence.evaluate_positive_eq_original E C q)

end M9Native.LagrangianFlagPolynomialLinear

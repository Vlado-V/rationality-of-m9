module

public import M9StacksIntegration.LagrangianFlagPolynomialLinear
public import M9StacksIntegration.LagrangianFlagMonomialPush
public import M9StacksIntegration.LagrangianFlagMonomialInput

/-!
# The actual free-six quotient-flag coefficient functional

All three integrations are the native proper pushforwards of the actual
projective bundles, in fibre dimensions five, four and three. Their
six surviving monomials, together with additivity, identify the actual
polynomial integral on every original Chow class. The final value16
is therefore a geometric push identity, rather than only a coefficient
calculation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow MvPolynomial
universe u
namespace M9Native.LagrangianFlagPolynomialPush
open LagrangianFlagCoefficientFunctional LagrangianFlagPowerStages
open LagrangianChowPolynomials LagrangianFlagPolynomialLinear LagrangianFlagMonomialPush

attribute [local instance] LagrangianFlagPowerStages.sourceFinite
  LagrangianFlagPowerStages.kernel1Rank LagrangianFlagPowerStages.kernel1Finite
  LagrangianFlagPowerStages.kernel2Rank LagrangianFlagPowerStages.kernel2Finite
  LagrangianFlagPowerStages.projection1LFT LagrangianFlagPowerStages.projection2LFT
  LagrangianFlagPowerStages.projection3LFT

variable {T : Scheme.{u}} (E : T.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 6]
    (C : ChowSituation.{u}) (q : T ⟶ C.S) [LocallyOfFiniteType q]

/-- Polynomial evaluation and the original three powers give the same
actual integral; only the displayed output grades are transported. -/
theorem integral_word_eq_monomialPush (a b c : ℕ) (hdeg : a+b+c=12)
    (k : ℤ) (α : chowGroup C q k) :
    integralMap E C q k α (X 0^a * X 1^b * X 2^c) =
      monomialPush E C q a b c hdeg k α := by
  apply eq_of_heq
  refine (integralMap_apply_heq E C q k α _).trans ?_
  have hindex := LineFamilyCapWords.family_apply_index_heq C (baseMap3 E C q)
    (evaluate C (baseMap3 E C q) (positiveLines E) (X 0^a * X 1^b * X 2^c))
    (k+12) hdeg.symm (flatPullClass E C q k α)
  have hinput := hindex.trans
    (LagrangianFlagMonomialInput.evaluate_monomial_flatPullClass E C q a b c k α)
  exact (triplePush_heq E C q (by omega) hinput).trans
    (chowGroupCast_heq C q _ _).symm

/-- Components outside cap degree twelve have zero actual integral. -/
theorem integral_word_zero_of_ne_twelve (a b c : ℕ) (hdeg : a+b+c≠12)
    (k : ℤ) (α : chowGroup C q k) :
    integralMap E C q k α (X 0^a * X 1^b * X 2^c) = 0 := by
  have hz := evaluate_word_homogeneous C (baseMap3 E C q) (positiveLines E) a b c
    (k+12) 12 (Ne.symm hdeg)
  change triplePush E C q k
    (chowGroupCast C (baseMap3 E C q) (by omega : (k+12)-(12:ℤ)=k)
      (evaluate C (baseMap3 E C q) (positiveLines E)
        (X 0^a * X 1^b * X 2^c) (k+12) 12 (flatPullClass E C q k α))) = 0
  rw [hz]
  change triplePush E C q k
    (chowGroupCast C (baseMap3 E C q) (by omega : (k+12)-(12:ℤ)=k)
      (0 : chowGroup C (baseMap3 E C q) ((k+12)-(12:ℤ)))) = 0
  rw [map_zero, map_zero]

variable (e : E ≅ SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin 6)))
include e

theorem integral_monomial_exponent_one (a b c : ℕ) (k : ℤ) (α : chowGroup C q k) :
    integralMap E C q k α (monomial (exponent a b c) (1:ℤ)) =
      functional (monomial (exponent a b c) (1:ℤ)) • α := by
  by_cases hdeg : a+b+c=12
  · rw [monomial_exponent_one, integral_word_eq_monomialPush E C q a b c hdeg,
      ← monomial_exponent_one, functional_monomial_one]
    by_cases h1 : a=5 ∧ b=4 ∧ c=3
    · rcases h1 with ⟨rfl,rfl,rfl⟩
      simpa using push543 (E:=E) (C:=C) (q:=q) (e:=e) k α
    by_cases h2 : a=4 ∧ b=5 ∧ c=3
    · rcases h2 with ⟨rfl,rfl,rfl⟩
      simpa using push453 (E:=E) (C:=C) (q:=q) (e:=e) k α
    by_cases h3 : a=5 ∧ b=3 ∧ c=4
    · rcases h3 with ⟨rfl,rfl,rfl⟩
      simpa using push534 (E:=E) (C:=C) (q:=q) (e:=e) k α
    by_cases h4 : a=3 ∧ b=5 ∧ c=4
    · rcases h4 with ⟨rfl,rfl,rfl⟩
      simpa using push354 (E:=E) (C:=C) (q:=q) (e:=e) k α
    by_cases h5 : a=4 ∧ b=3 ∧ c=5
    · rcases h5 with ⟨rfl,rfl,rfl⟩
      simpa using push435 (E:=E) (C:=C) (q:=q) (e:=e) k α
    by_cases h6 : a=3 ∧ b=4 ∧ c=5
    · rcases h6 with ⟨rfl,rfl,rfl⟩
      simpa using push345 (E:=E) (C:=C) (q:=q) (e:=e) k α
    have hz := monomialPush_zero (E:=E) (C:=C) (q:=q) (e:=e)
      a b c hdeg (by tauto) k α
    simpa only [ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,
      ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,
      sub_self,sub_zero,add_zero,zero_zsmul] using hz
  · rw [monomial_exponent_one,integral_word_zero_of_ne_twelve E C q a b c hdeg,
      ← monomial_exponent_one,functional_monomial_one_of_ne_twelve a b c hdeg,zero_zsmul]

/-- The actual geometric integration map equals the six original
integer coefficients acting on the SAME original class. -/
theorem integralMap_eq_functional (k : ℤ) (α : chowGroup C q k) (p : Polynomial3) :
    integralMap E C q k α p = functional p • α := by
  have hmaps : integralMap E C q k α = functionalClassMap C q k α := by
    apply AddMonoidHom.ext
    intro f
    induction f using MvPolynomial.induction_on' with
    | monomial d r =>
        have h1 : integralMap E C q k α (monomial d (1:ℤ)) =
            functionalClassMap C q k α (monomial d (1:ℤ)) := by
          change integralMap E C q k α (monomial d (1:ℤ)) =
            functional (monomial d (1:ℤ)) • α
          simpa only [exponent_coordinates] using
            integral_monomial_exponent_one (E:=E) (C:=C) (q:=q) (e:=e)
              (d 0) (d 1) (d 2) k α
        rw [monomial_eq_zsmul, map_zsmul, map_zsmul, h1]
    | add f g hf hg =>
        rw [map_add, map_add, hf, hg]
  exact congrArg (fun h : Polynomial3 →+ chowGroup C q k => h p) hmaps

/-- Genuine three-stage geometric integration of the normalized LG
integrand is sixteen times the original class. -/
theorem integrand_integral (k : ℤ) (α : chowGroup C q k) :
    integralMap E C q k α integrand = 16 • α := by
  rw [integralMap_eq_functional (E:=E) (C:=C) (q:=q) (e:=e),functional_integrand]
  simp only [ofNat_zsmul]

/-- The same actual value in the ORIGINAL three native named flag lines. -/
theorem original_integrand_integral (k : ℤ) (α : chowGroup C q k) :
    triplePush E C q k
      (chowGroupCast C (baseMap3 E C q) (by omega)
        (evaluate C (baseMap3 E C q)
          (LagrangianPolynomialLineCongruence.originalLines E) integrand
          (k+12) 12 (flatPullClass E C q k α))) = 16 • α :=
  (integralMap_eq_original E C q k α integrand).symm.trans
    (integrand_integral (E:=E) (C:=C) (q:=q) (e:=e) k α)

end M9Native.LagrangianFlagPolynomialPush

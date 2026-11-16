module

public import M9StacksIntegration.LagrangianFlagChernNumerator
public import M9StacksIntegration.LagrangianChowPolynomials
public import M9StacksIntegration.LagrangianFlagCoefficientFunctional

/-!
# The genuine determinant/top-Chern flag integrand

The polynomial is evaluated only in the actual line-generated cap
subring. Its factors are the proved original determinant and original
exterior-square top Chern component. Thus the integrand is attached to
actual Chow operations, without a root realization premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.LagrangianFlagPolynomialNumerator

open ChowCapWords GradedLineCapSubring LagrangianChowPolynomials
open LagrangianFlagChernNumerator

attribute [local instance] LagrangianFlagChernNumerator.sourceExteriorRank
  LagrangianFlagChernNumerator.pulledExteriorRank

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} D]

/-- The original named positive quotient lines, in their original order. -/
def originalLines : Fin 3 → InvertibleLine (FlagThreeQuotient.space D) :=
  ![firstLine D,secondLine D,thirdLine D]

def sumPolynomial : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2

def pairPolynomial : MvPolynomial (Fin 3) ℤ :=
  (MvPolynomial.X 0 + MvPolynomial.X 1) *
    (MvPolynomial.X 0 + MvPolynomial.X 2) *
    (MvPolynomial.X 1 + MvPolynomial.X 2)

/-- The original ambient determinant-six/top-Chern-three numerator. -/
def numeratorPolynomial : MvPolynomial (Fin 3) ℤ := sumPolynomial ^ 6 * pairPolynomial

variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]
  (C : ChowSituation.{u})
  (q : FlagThreeQuotient.space D ⟶ C.S) [LocallyOfFiniteType q]

local instance nativeExteriorRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (Scheme.Modules.exteriorPower D 2) 3 := by
  simpa only [show Nat.choose 3 2 = 3 by decide,Nat.cast_ofNat] using
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower D 3 2

local instance nativePulledExteriorRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj
        (Scheme.Modules.exteriorPower D 2)) 3 :=
  @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (FlagThreeQuotient.space D) X
    (FlagThreeQuotient.projection D) (Scheme.Modules.exteriorPower D 2) 3 (nativeExteriorRank D)

theorem evaluate_numeratorPolynomial :
    evaluate C q (originalLines D) numeratorPolynomial =
      lineFamily C q (pulledDeterminantLine D) ^ 6 *
        homComponent 3 (chernFamily C q
          ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj
            (Scheme.Modules.exteriorPower D 2)) 3) := by
  have hExterior : homComponent 3 (chernFamily C q
      ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj
        (Scheme.Modules.exteriorPower D 2)) 3) =
      (lineFamily C q (firstLine D) + lineFamily C q (secondLine D)) *
        (lineFamily C q (firstLine D) + lineFamily C q (thirdLine D)) *
        (lineFamily C q (secondLine D) + lineFamily C q (thirdLine D)) := by
    simpa only [MukaiBundleDeterminant.topExterior,Nat.cast_ofNat] using
      pulledExteriorSquare_pair_lineFamilies D C q
  rw [pulledDeterminant_lineFamily,hExterior]
  let φ := evaluate C q (originalLines D)
  have hSum : φ sumPolynomial =
      lineFamily C q (firstLine D) + lineFamily C q (secondLine D) +
        lineFamily C q (thirdLine D) := by
    rw [sumPolynomial,φ.map_add,φ.map_add]
    simp only [φ,evaluate_X]
    rfl
  have hPairs : φ pairPolynomial =
      (lineFamily C q (firstLine D) + lineFamily C q (secondLine D)) *
        (lineFamily C q (firstLine D) + lineFamily C q (thirdLine D)) *
        (lineFamily C q (secondLine D) + lineFamily C q (thirdLine D)) := by
    rw [pairPolynomial,φ.map_mul,φ.map_mul,φ.map_add,φ.map_add,φ.map_add]
    simp only [φ,evaluate_X]
    rfl
  exact (φ.map_mul (sumPolynomial ^ 6) pairPolynomial).trans
    (congrArg₂ (· * ·) ((φ.map_pow sumPolynomial 6).trans (congrArg (· ^ 6) hSum)) hPairs)

/-- The actual normalized flag polynomial is the actual x²y normalizer
composed with the pulled original Grassmannian numerator. -/
theorem evaluate_integrand :
    evaluate C q (originalLines D) LagrangianFlagCoefficientFunctional.integrand =
      (lineFamily C q (firstLine D) ^ 2 * lineFamily C q (secondLine D)) *
        (lineFamily C q (pulledDeterminantLine D) ^ 6 *
          homComponent 3 (chernFamily C q
            ((Scheme.Modules.pullback (FlagThreeQuotient.projection D)).obj
              (Scheme.Modules.exteriorPower D 2)) 3)) := by
  have hPolynomial : LagrangianFlagCoefficientFunctional.integrand =
      (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) * numeratorPolynomial := by
    unfold LagrangianFlagCoefficientFunctional.integrand numeratorPolynomial
      sumPolynomial pairPolynomial
    ring
  rw [hPolynomial,(evaluate C q (originalLines D)).map_mul,
    evaluate_numeratorPolynomial,(evaluate C q (originalLines D)).map_mul,
    (evaluate C q (originalLines D)).map_pow,evaluate_X,evaluate_X]
  rfl

end M9Native.LagrangianFlagPolynomialNumerator

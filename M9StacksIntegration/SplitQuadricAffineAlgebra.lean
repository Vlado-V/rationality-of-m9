module

public import M9StacksIntegration.LagrangianKernelFiveMinorNormalization

/-!
# Explicit affine polynomial quotients for the split quadric

The four formulas are the dehomogenizations at coordinates 3,2,0,4
of X0*X2-X1^2-X3*X4. The actual quotient algebras are isomorphic to
three-variable polynomial algebras, with both maps given on generators.
The construction works over every commutative coefficient ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open MvPolynomial

universe u

namespace M9Native.SplitQuadricAffineAlgebra

variable (R : Type u) [CommRing R]

abbrev PolynomialFour := MvPolynomial (Fin 4) R
abbrev PolynomialThree := MvPolynomial (Fin 3) R

/-- Pivot order matching the four genuine common-kernel charts. -/
def pivot : Fin 4 → Fin 5 := ![3,2,0,4]

/-- Literal standard-chart equations in the ordinary order of the remaining coordinates. -/
def dehomPolynomial : Fin 4 → PolynomialFour R :=
  ![X 0 * X 2 - (X 1)^2 - X 3,
    X 0 - (X 1)^2 - X 2 * X 3,
    X 1 - (X 0)^2 - X 2 * X 3,
    X 0 * X 2 - (X 1)^2 - X 3]

/-- Actual dehomogeneous coordinates of the four parametrizations. -/
def chartVariables : Fin 4 → Fin 4 → PolynomialThree R :=
  ![![X 2, -X 1, X 0, X 0 * X 2 - (X 1)^2],
    ![-X 0 * X 2 + (X 1)^2, -X 1, -X 0, X 2],
    ![-X 1, -X 0 * X 2 + (X 1)^2, -X 2, X 0],
    ![-X 0, -X 1, -X 2, X 0 * X 2 - (X 1)^2]]

/-- The inverse coordinates are genuine polynomials, with no division. -/
def inverseVariables : Fin 4 → Fin 3 → PolynomialFour R :=
  ![![X 2, -X 1, X 0], ![-X 2, -X 1, X 3],
    ![X 3, -X 0, -X 2], ![-X 0, -X 1, -X 2]]

def chartMap (c : Fin 4) : PolynomialFour R →ₐ[R] PolynomialThree R :=
  MvPolynomial.aeval (chartVariables R c)

theorem chartMap_equation (c : Fin 4) : chartMap R c (dehomPolynomial R c) = 0 := by
  fin_cases c <;> simp [chartMap, dehomPolynomial, chartVariables] <;> ring

def chartIdeal (c : Fin 4) : Ideal (PolynomialFour R) :=
  Ideal.span {dehomPolynomial R c}

def quotientToAffine (c : Fin 4) :
    PolynomialFour R ⧸ chartIdeal R c →ₐ[R] PolynomialThree R :=
  Ideal.Quotient.liftₐ (chartIdeal R c) (chartMap R c) (by
    change Ideal.span {dehomPolynomial R c} ≤ RingHom.ker (chartMap R c).toRingHom
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact chartMap_equation R c)

def affineToQuotient (c : Fin 4) :
    PolynomialThree R →ₐ[R] PolynomialFour R ⧸ chartIdeal R c :=
  MvPolynomial.aeval fun i => Ideal.Quotient.mk (chartIdeal R c) (inverseVariables R c i)

@[simp] theorem quotientToAffine_mk (c : Fin 4) (p : PolynomialFour R) :
    quotientToAffine R c (Ideal.Quotient.mk (chartIdeal R c) p) = chartMap R c p := rfl

theorem quotientToAffine_comp_affineToQuotient (c : Fin 4) :
    (quotientToAffine R c).comp (affineToQuotient R c) = AlgHom.id R (PolynomialThree R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, affineToQuotient,
    MvPolynomial.aeval_X, quotientToAffine_mk]
  fin_cases c <;> fin_cases i <;> simp [chartMap, inverseVariables, chartVariables]

theorem affineToQuotient_comp_quotientToAffine (c : Fin 4) :
    (affineToQuotient R c).comp (quotientToAffine R c) =
      AlgHom.id R (PolynomialFour R ⧸ chartIdeal R c) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change affineToQuotient R c (chartMap R c (X i)) =
    Ideal.Quotient.mk (chartIdeal R c) (X i)
  have hq : Ideal.Quotient.mk (chartIdeal R c) (dehomPolynomial R c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [chartMap, MvPolynomial.aeval_X]
  fin_cases c <;> fin_cases i <;>
    simp [affineToQuotient, inverseVariables, chartVariables, dehomPolynomial] at hq ⊢ <;>
    first | linear_combination hq | linear_combination -hq

/-- The genuine affine chart quotient, retaining all nilpotents over R. -/
def chartEquiv (c : Fin 4) :
    (PolynomialFour R ⧸ chartIdeal R c) ≃ₐ[R] PolynomialThree R :=
  AlgEquiv.ofAlgHom (quotientToAffine R c) (affineToQuotient R c)
    (quotientToAffine_comp_affineToQuotient R c) (affineToQuotient_comp_quotientToAffine R c)

theorem chartEquiv_mk (c : Fin 4) (p : PolynomialFour R) :
    chartEquiv R c (Ideal.Quotient.mk (chartIdeal R c) p) = chartMap R c p := rfl

end M9Native.SplitQuadricAffineAlgebra

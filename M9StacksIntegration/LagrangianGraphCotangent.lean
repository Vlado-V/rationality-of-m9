module

public import M9StacksIntegration.LagrangianGraphDifferentials
public import M9StacksIntegration.LagrangianChartCotangent

/-! Actual invertibility of the intrinsic symmetric graph differential,
computed using the polynomial Kähler basis. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators TensorProduct

namespace M9Native.LagrangianGraphCotangent

open LagrangianCotangentFormula LagrangianInfinitesimal LagrangianGraphDifferentials
open LagrangianSymmetricCongruence LagrangianSymmetricSquare

variable {k R M : Type*} [CommRing k] [CommRing R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M]

/-- The graph map is determined by its literal coordinate differentials. -/
theorem graphSquareMap_eq_basisEquiv (d : Derivation k R M) (A : symmetricMatrices R)
    (b : Basis (Fin 6) R M)
    (hb : ∀ i,d (A.val (upperPair i).2 (upperPair i).1)=b i) :
    graphSquareMap R d A=((monomialBasis R).equiv b (Equiv.refl _)).toLinearMap := by
  apply (monomialBasis R).ext
  intro i
  rw [graphSquareMap_monomial,hb]
  simp

theorem graphSquareMap_bijective (d : Derivation k R M) (A : symmetricMatrices R)
    (b : Basis (Fin 6) R M)
    (hb : ∀ i,d (A.val (upperPair i).2 (upperPair i).1)=b i) :
    Function.Bijective (graphSquareMap R d A) := by
  rw [graphSquareMap_eq_basisEquiv d A b hb]
  exact LinearEquiv.bijective _

variable (K : Type*) [CommRing K]

/-- The actual symmetric polynomial matrix in the six upper-entry coordinates. -/
def genericMatrix : symmetricMatrices (MvPolynomial (Fin 6) K) :=
  (coordinates (MvPolynomial (Fin 6) K)).symm (fun i => MvPolynomial.X i)

theorem genericMatrix_upper (i : Fin 6) :
    (genericMatrix K).val (upperPair i).2 (upperPair i).1=MvPolynomial.X i := by
  fin_cases i <;> rfl

/-- The intrinsic graph symmetric-square map to the actual polynomial
Kähler module is an isomorphism over any commutative base ring. -/
theorem genericGraphSquareMap_bijective :
    Function.Bijective (graphSquareMap (MvPolynomial (Fin 6) K)
      (KaehlerDifferential.D K (MvPolynomial (Fin 6) K)) (genericMatrix K)) := by
  apply graphSquareMap_bijective _ _ (KaehlerDifferential.mvPolynomialBasis K (Fin 6))
  intro i
  rw [genericMatrix_upper]
  simp only [KaehlerDifferential.mvPolynomialBasis_apply]

end M9Native.LagrangianGraphCotangent

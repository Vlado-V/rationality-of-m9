module

public import M9StacksIntegration.LagrangianCotangentFormula
public import M9StacksIntegration.LagrangianSymmetricSquareEquivariance

/-! Literal differential coefficients on the actual symmetric graph chart. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators TensorProduct

namespace M9Native.LagrangianGraphDifferentials

open LagrangianCotangentFormula LagrangianInfinitesimal
open LagrangianSymmetricCongruence LagrangianSymmetricSquare

variable (R : Type*) [CommRing R]

/-- The literal dual coefficient map of the quotient `[I|A]`. -/
def graphCoefficients (A : Matrix (Fin 3) (Fin 3) R) :
    (Fin 3 → R) →ₗ[R] (Fin 6 → R) :=
  LinearMap.pi (fun j => Fin.addCases (fun i => LinearMap.proj i)
    (fun i => ∑ k : Fin 3,A k i • LinearMap.proj k) j)

@[simp] theorem graphCoefficients_left (A : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (i : Fin 3) : graphCoefficients R A v (i.castAdd 3)=v i := by
  simp [graphCoefficients]

@[simp] theorem graphCoefficients_right (A : Matrix (Fin 3) (Fin 3) R)
    (v : Fin 3 → R) (i : Fin 3) :
    graphCoefficients R A v (Fin.natAdd 3 i)=∑ k : Fin 3,A k i*v k := by
  change (Fin.addCases (motive := fun _ : Fin 6 => (Fin 3 → R) →ₗ[R] R)
    (fun i => LinearMap.proj i)
    (fun i => ∑ k : Fin 3,A k i • LinearMap.proj k) (Fin.natAdd 3 i)) v=_
  rw [Fin.addCases_right]
  simp [Finset.sum_apply,smul_eq_mul]

/-- Actual symmetry of `A` proves actual isotropy of its graph. -/
theorem graphCoefficients_isotropic (A : symmetricMatrices R) (v w : Fin 3 → R) :
    symplecticPair (graphCoefficients R A.val v) (graphCoefficients R A.val w)=0 := by
  have hA (i j : Fin 3) : A.val i j=A.val j i := (congrFun (congrFun A.property i) j).symm
  simp only [symplecticPair,graphCoefficients_left,graphCoefficients_right,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  norm_num only [Fin.reduceSucc] at *
  simp only [hA 1 0,hA 2 0,hA 2 1]
  ring

variable {k M : Type*} [CommRing k] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M]

/-- On the actual constant dual basis the intrinsic formula is the
literal coordinate differential, with no off-diagonal normalization. -/
theorem differentialPair_graph_basis (d : Derivation k R M)
    (A : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    differentialPair d (graphCoefficients R A) (Pi.single i 1) (Pi.single j 1)=d (A j i) := by
  simp only [differentialPair,graphCoefficients_left,graphCoefficients_right]
  fin_cases i <;> fin_cases j
  all_goals simp [Fin.sum_univ_succ,Pi.single_apply]

/-- The genuine native symmetric-square map of the graph chart. -/
def graphSquareMap (d : Derivation k R M) (A : symmetricMatrices R) :
    Square R →ₗ[R] M :=
  SymPow.sqLift (intrinsicBilinear d (graphCoefficients R A.val)
    (graphCoefficients_isotropic R A))
    (intrinsicBilinear_symmetric d (graphCoefficients R A.val) (graphCoefficients_isotropic R A))

theorem graphSquareMap_monomial (d : Derivation k R M) (A : symmetricMatrices R) (i : Fin 6) :
    graphSquareMap R d A (monomialBasis R i)=
      d (A.val (upperPair i).2 (upperPair i).1) := by
  rw [monomialBasis_eq_product]
  change SymPow.sqLift _ _ (SymPow.sqMul LinearMap.id
    (Pi.single (upperPair i).1 1 ⊗ₜ[R] Pi.single (upperPair i).2 1))=_
  rw [SymPow.sqLift_sqMul_tmul]
  exact differentialPair_graph_basis R d A.val _ _

end M9Native.LagrangianGraphDifferentials

module

public import M9StacksIntegration.LagrangianSymmetricCongruence
public import StacksFrontier.LinearAlgebra.SymmetricPower.MonomialBasis

/-!
# The genuine symmetric square in the LG tangent coordinates

The source is the actual degree-two piece of the native symmetric
algebra. The coordinate isomorphism uses the standard symmetrization
convention: a mixed monomial maps to half the corresponding symmetric
matrix. Thus the diagonal and off-diagonal normalizations are explicit.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianSymmetricSquare

open LagrangianInfinitesimal LagrangianSymmetricCongruence

abbrev QuadraticIndex := {d : Fin 3 →₀ ℕ // d.degree=2}

/-- The six literal quadratic monomial exponents in upper-entry order. -/
def quadraticIndex (i : Fin 6) : QuadraticIndex :=
  ⟨Finsupp.single (upperPair i).1 1+Finsupp.single (upperPair i).2 1,by
    rw [map_add,Finsupp.degree_single,Finsupp.degree_single]⟩

theorem quadraticIndex_injective : Function.Injective quadraticIndex := by
  intro i j h
  have ht := congrArg (fun d : QuadraticIndex => (d.val 0,d.val 1)) h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    simp [quadraticIndex,upperPair,Finsupp.single_apply] at ht

theorem quadraticIndex_surjective : Function.Surjective quadraticIndex := by
  intro d
  have hd := d.property
  simp only [Finsupp.degree_eq_sum,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hd
  change d.val 0+(d.val 1+d.val 2)=2 at hd
  have hp :
      (d.val 0=2 ∧ d.val 1=0 ∧ d.val 2=0) ∨
      (d.val 0=1 ∧ d.val 1=1 ∧ d.val 2=0) ∨
      (d.val 0=1 ∧ d.val 1=0 ∧ d.val 2=1) ∨
      (d.val 0=0 ∧ d.val 1=2 ∧ d.val 2=0) ∨
      (d.val 0=0 ∧ d.val 1=1 ∧ d.val 2=1) ∨
      (d.val 0=0 ∧ d.val 1=0 ∧ d.val 2=2) := by omega
  rcases hp with h|h|h|h|h|h
  · refine ⟨0,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [quadraticIndex,upperPair,h.1,h.2.1,h.2.2]
  · refine ⟨1,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [quadraticIndex,upperPair,h.1,h.2.1,h.2.2]
  · refine ⟨2,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [quadraticIndex,upperPair,h.1,h.2.1,h.2.2]
  · refine ⟨3,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [quadraticIndex,upperPair,h.1,h.2.1,h.2.2]
  · refine ⟨4,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [quadraticIndex,upperPair,h.1,h.2.1,h.2.2]
  · refine ⟨5,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [quadraticIndex,upperPair,h.1,h.2.1,h.2.2]

def quadraticIndexEquiv : Fin 6 ≃ QuadraticIndex :=
  Equiv.ofBijective quadraticIndex ⟨quadraticIndex_injective,quadraticIndex_surjective⟩

variable (R : Type u) [CommRing R]

abbrev Square := SymPow.symmetricPower 2 R (Fin 3 → R)

/-- The actual native symmetric-square monomial basis, with its six
exponents explicitly enumerated. -/
def monomialBasis : Basis (Fin 6) R (Square R) :=
  (SymPow.basisSymmetricPower (Pi.basisFun R (Fin 3)) 2).reindex quadraticIndexEquiv.symm

/-- Each enumerated basis vector is its literal product in the native
symmetric algebra. -/
theorem monomialBasis_coe (i : Fin 6) :
    (monomialBasis R i : SymmetricAlgebra R (Fin 3 → R))=
      SymmetricAlgebra.ι R (Fin 3 → R) (Pi.single (upperPair i).1 1)*
        SymmetricAlgebra.ι R (Fin 3 → R) (Pi.single (upperPair i).2 1) := by
  simp only [monomialBasis,Module.Basis.reindex_apply,Equiv.symm_symm]
  change (SymPow.basisSymmetricPower (Pi.basisFun R (Fin 3)) 2 (quadraticIndex i) :
    SymmetricAlgebra R (Fin 3 → R))= _
  rw [SymPow.coe_basisSymmetricPower_apply_eq_prod_univ]
  fin_cases i <;>
    simp [quadraticIndex,upperPair,Fin.prod_univ_succ,Finsupp.single_apply,pow_two]

section Half

variable [Invertible (2 : R)]

/-- The monomial-to-matrix normalization, including the mixed factors. -/
def halfCoordinates : (Fin 6 → R) ≃ₗ[R] (Fin 6 → R) where
  toFun v := ![v 0,⅟(2:R)*v 1,⅟(2:R)*v 2,v 3,⅟(2:R)*v 4,v 5]
  invFun v := ![v 0,(2:R)*v 1,(2:R)*v 2,v 3,(2:R)*v 4,v 5]
  left_inv v := by
    funext i
    fin_cases i <;> simp [← mul_assoc]
  right_inv v := by
    funext i
    fin_cases i <;> simp [← mul_assoc]
  map_add' v w := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' r v := by
    funext i
    fin_cases i <;> simp [mul_left_comm]

/-- The genuine symmetric square is identified with the actual tangent
matrix module, in its natural symmetrization normalization. -/
def squareEquivMatrices : Square R ≃ₗ[R] symmetricMatrices R :=
  (monomialBasis R).equivFun.trans ((halfCoordinates R).trans (coordinates R).symm)

end Half

end M9Native.LagrangianSymmetricSquare

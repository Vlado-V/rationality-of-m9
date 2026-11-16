module

public import M9StacksIntegration.LagrangianGraphCotangent

/-! The genuine frozen native six-variable chart numbering, with the
actual intrinsic graph map and the actual polynomial Kähler basis. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Matrix Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianNativeGraphCotangent

open LagrangianInfinitesimal LagrangianGraphDifferentials LagrangianGraphCotangent
open LagrangianMatrixChart LagrangianSymmetricCongruence

theorem upperPair_ordered (i : Fin 6) : (upperPair i).1≤(upperPair i).2 := by
  fin_cases i <;> decide

def upperPairIndex (i : Fin 6) : ULift.{u} SymmetricEntry :=
  ULift.up ⟨upperPair i,upperPair_ordered i⟩

theorem upperPairIndex_bijective : Function.Bijective (upperPairIndex.{u}) := by
  constructor
  · intro i j hij
    have h := congrArg (fun p : ULift.{u} SymmetricEntry => p.down.val) hij
    fin_cases i <;> fin_cases j <;> simp_all [upperPairIndex,upperPair]
  · rintro ⟨⟨⟨i,j⟩,hij⟩⟩
    fin_cases i <;> fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · norm_num at hij
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · norm_num at hij
    · norm_num at hij
    · exact ⟨5,rfl⟩

/-- The permutation from literal upper-pair order to the original
native variable numbering, rather than an assumed agreement of frames. -/
def nativeVariableEquiv : Fin 6 ≃ Fin 6 :=
  (Equiv.ofBijective upperPairIndex.{u} upperPairIndex_bijective).trans
    symmetricEntryEquivFinSix.{u}

variable (K : Type u) [CommRing K]

/-- Exactly the polynomial entries occurring in the checked original
big-cell quotient. -/
def nativeMatrix : symmetricMatrices (MvPolynomial (Fin 6) K) :=
  ⟨fun i j => MvPolynomial.X
    (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j)))),by
    funext i j
    change (MvPolynomial.X
      (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (j,i)))) : MvPolynomial (Fin 6) K)=_
    rw [symmetricIndex_swap]⟩

theorem nativeMatrix_upper (i : Fin 6) :
    (nativeMatrix K).val (upperPair i).2 (upperPair i).1=
      MvPolynomial.X (nativeVariableEquiv.{u} i) := by
  change (MvPolynomial.X
    (symmetricEntryEquivFinSix (ULift.up.{u}
      (symmetricIndex ((upperPair i).2,(upperPair i).1)))) : MvPolynomial (Fin 6) K)=_
  rw [symmetricIndex_swap]
  simp only [symmetricIndex,upperPair_ordered,dite_true,nativeVariableEquiv,
    Equiv.trans_apply,Equiv.ofBijective_apply,upperPairIndex]

/-- The native chart's exact intrinsic graph differential is bijective:
the actual Kähler basis is merely permuted by the proven variable map. -/
theorem nativeGraphSquareMap_bijective :
    Function.Bijective (graphSquareMap (MvPolynomial (Fin 6) K)
      (KaehlerDifferential.D K (MvPolynomial (Fin 6) K)) (nativeMatrix K)) := by
  apply graphSquareMap_bijective _ _
    ((KaehlerDifferential.mvPolynomialBasis K (Fin 6)).reindex nativeVariableEquiv.{u}.symm)
  intro i
  rw [nativeMatrix_upper]
  simp only [Basis.reindex_apply,Equiv.symm_symm,KaehlerDifferential.mvPolynomialBasis_apply]

end M9Native.LagrangianNativeGraphCotangent

module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Tactic

/-!
# Explicit symplectic completion of an actual isotropic quotient matrix

An actual right inverse of `M` gives columns `R`; the columns `C=J Mᵀ`
span the symplectic partners in its kernel. An upper-triangular correction
of `Rᵀ J R` makes the section columns isotropic. Consequently `[R'|C]`
is an actual symplectic matrix and `M [R'|C]=[I|0]`.
The construction works over any commutative ring admitting the given
right inverse, including characteristic two.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open Matrix

universe u v

namespace M9Native.LagrangianSymplecticMatrix

variable {n : Type v} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommRing R]

section UpperPart
variable [LinearOrder n]

/-- The strictly upper-triangular part of an actual matrix. -/
def upperPart (A : Matrix n n R) : Matrix n n R := fun i j => if i < j then A i j else 0

omit [Fintype n] [DecidableEq n] in
/-- Every alternating matrix is the difference of its upper part and its transpose. -/
theorem upperPart_sub_transpose (A : Matrix n n R) (hskew : Aᵀ = -A)
    (hdiag : ∀ i, A i i=0) : upperPart A - (upperPart A)ᵀ = A := by
  ext i j
  have hji : A j i = -A i j := congrFun (congrFun hskew i) j
  by_cases hij : i < j
  · simp [upperPart,hij,not_lt_of_gt hij]
  · by_cases hji' : j < i
    · simp [upperPart,hij,hji',hji]
    · have he : i=j := le_antisymm (le_of_not_gt hji') (le_of_not_gt hij)
      subst j
      simp [upperPart,hdiag]

end UpperPart

/-- The actual pullback of the native standard alternating form along a matrix. -/
def gram (A : Matrix (n ⊕ n) n R) : Matrix n n R := Aᵀ * Matrix.J n R * A

theorem gram_transpose (A : Matrix (n ⊕ n) n R) : (gram A)ᵀ = -gram A := by
  simp [gram,Matrix.transpose_mul,Matrix.J_transpose,Matrix.mul_assoc]

theorem gram_blocks (A : Matrix (n ⊕ n) n R) :
    gram A = A.toRows₂ᵀ * A.toRows₁ - A.toRows₁ᵀ * A.toRows₂ := by
  calc
    gram A = gram (Matrix.fromRows A.toRows₁ A.toRows₂) :=
      congrArg gram (Matrix.fromRows_toRows A).symm
    _ = _ := by
      unfold gram
      rw [Matrix.transpose_fromRows,Matrix.J,Matrix.mul_assoc,Matrix.fromBlocks_mul_fromRows,
        Matrix.fromCols_mul_fromRows]
      simp only [Matrix.zero_mul,Matrix.neg_mul,Matrix.one_mul,zero_add,add_zero,Matrix.mul_neg]
      abel

theorem gram_diag (A : Matrix (n ⊕ n) n R) (i : n) : gram A i i=0 := by
  rw [gram_blocks]
  simp [Matrix.mul_apply,Matrix.transpose_apply,mul_comm]

/-- The actual kernel partner columns determined by the quotient matrix. -/
def partner (M : Matrix n (n ⊕ n) R) : Matrix (n ⊕ n) n R := Matrix.J n R * Mᵀ

theorem quotient_partner (M : Matrix n (n ⊕ n) R)
    (hiso : M * Matrix.J n R * Mᵀ=0) : M * partner M=0 := by
  simpa only [partner,Matrix.mul_assoc] using hiso

theorem section_partner (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) : Sᵀ * Matrix.J n R * partner M = -1 := by
  calc
    _ = Sᵀ * (Matrix.J n R * Matrix.J n R) * Mᵀ := by simp [partner,Matrix.mul_assoc]
    _ = -(M*S)ᵀ := by rw [Matrix.J_squared,Matrix.transpose_mul]; simp
    _ = _ := by rw [hMS,Matrix.transpose_one]

theorem partner_section (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) : (partner M)ᵀ * Matrix.J n R * S = 1 := by
  calc
    _ = M * ((Matrix.J n R)ᵀ * Matrix.J n R) * S := by
      simp [partner,Matrix.transpose_mul,Matrix.mul_assoc]
    _ = M*S := by rw [Matrix.J_transpose,Matrix.neg_mul,Matrix.J_squared]; simp
    _ = _ := hMS

theorem partner_isotropic (M : Matrix n (n ⊕ n) R)
    (hiso : M * Matrix.J n R * Mᵀ=0) : gram (partner M)=0 := by
  calc
    _ = M * ((Matrix.J n R)ᵀ * Matrix.J n R * Matrix.J n R) * Mᵀ := by
      simp [gram,partner,Matrix.transpose_mul,Matrix.mul_assoc]
    _ = M * Matrix.J n R * Mᵀ := by
      rw [Matrix.J_transpose,Matrix.neg_mul,Matrix.J_squared]
      simp
    _ = _ := hiso

variable [LinearOrder n]

/-- The corrected section, constructed from actual matrix products and a triangular part. -/
def correctedSection (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R) :
    Matrix (n ⊕ n) n R := S + partner M * upperPart (gram S)

theorem quotient_correctedSection (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) (hiso : M * Matrix.J n R * Mᵀ=0) : M * correctedSection M S=1 := by
  rw [correctedSection,Matrix.mul_add,← Matrix.mul_assoc,quotient_partner M hiso,hMS]
  simp

omit [LinearOrder n] in
theorem gram_add_partner (S C : Matrix (n ⊕ n) n R) (T : Matrix n n R) :
    gram (S+C*T) = gram S + (Sᵀ * Matrix.J n R * C)*T +
      Tᵀ*(Cᵀ * Matrix.J n R * S) + Tᵀ*(gram C)*T := by
  simp only [gram,Matrix.transpose_add,Matrix.transpose_mul,Matrix.add_mul,Matrix.mul_add,
    Matrix.mul_assoc]
  abel

theorem correctedSection_isotropic (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) (hiso : M * Matrix.J n R * Mᵀ=0) : gram (correctedSection M S)=0 := by
  rw [correctedSection,gram_add_partner,section_partner M S hMS,partner_section M S hMS,
    partner_isotropic M hiso]
  simp only [Matrix.neg_mul,Matrix.one_mul,Matrix.mul_one,Matrix.mul_zero,Matrix.zero_mul,add_zero]
  have hT := upperPart_sub_transpose (gram S) (gram_transpose S) (gram_diag S)
  calc
    _ = (upperPart (gram S) - (upperPart (gram S))ᵀ) + -upperPart (gram S) +
        (upperPart (gram S))ᵀ :=
      congrArg (fun A => A + -upperPart (gram S) + (upperPart (gram S))ᵀ) hT.symm
    _ = 0 := by abel

theorem correctedSection_partner (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) (hiso : M * Matrix.J n R * Mᵀ=0) :
    (correctedSection M S)ᵀ * Matrix.J n R * partner M = -1 := by
  calc
    _ = Sᵀ * Matrix.J n R * partner M +
        (upperPart (gram S))ᵀ * gram (partner M) := by
      simp [correctedSection,gram,Matrix.transpose_add,Matrix.transpose_mul,Matrix.add_mul,
        Matrix.mul_assoc]
    _ = _ := by rw [section_partner M S hMS,partner_isotropic M hiso]; simp

theorem partner_correctedSection (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) (hiso : M * Matrix.J n R * Mᵀ=0) :
    (partner M)ᵀ * Matrix.J n R * correctedSection M S = 1 := by
  calc
    _ = (partner M)ᵀ * Matrix.J n R * S + gram (partner M) * upperPart (gram S) := by
      simp [correctedSection,gram,Matrix.mul_add,Matrix.mul_assoc]
    _ = _ := by rw [partner_section M S hMS,partner_isotropic M hiso]; simp

/-- The actual completed symplectic matrix. -/
def completion (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R) :
    Matrix (n ⊕ n) (n ⊕ n) R := Matrix.fromCols (correctedSection M S) (partner M)

theorem completion_symplectic (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) (hiso : M * Matrix.J n R * Mᵀ=0) :
    completion M S ∈ Matrix.symplecticGroup n R := by
  rw [SymplecticGroup.mem_iff']
  unfold completion
  rw [Matrix.transpose_fromCols,Matrix.fromRows_mul,Matrix.fromRows_mul_fromCols]
  change Matrix.fromBlocks (gram (correctedSection M S))
    ((correctedSection M S)ᵀ * Matrix.J n R * partner M)
    ((partner M)ᵀ * Matrix.J n R * correctedSection M S) (gram (partner M)) = _
  rw [correctedSection_isotropic M S hMS hiso,correctedSection_partner M S hMS hiso,
    partner_correctedSection M S hMS hiso,partner_isotropic M hiso]
  rfl

theorem quotient_completion (M : Matrix n (n ⊕ n) R) (S : Matrix (n ⊕ n) n R)
    (hMS : M*S=1) (hiso : M * Matrix.J n R * Mᵀ=0) :
    M * completion M S = Matrix.fromCols 1 0 := by
  rw [completion,Matrix.mul_fromCols,quotient_correctedSection M S hMS hiso,quotient_partner M hiso]

/-- An actual surjective isotropic quotient admits a constructed symplectic normal form. -/
theorem exists_symplectic_normalForm (M : Matrix n (n ⊕ n) R)
    (hsurj : Function.Surjective M.mulVec) (hiso : M * Matrix.J n R * Mᵀ=0) :
    ∃ g : Matrix.symplecticGroup n R, M * (g : Matrix (n ⊕ n) (n ⊕ n) R)=Matrix.fromCols 1 0 := by
  obtain ⟨S,hMS⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
  exact ⟨⟨completion M S,completion_symplectic M S hMS hiso⟩,quotient_completion M S hMS hiso⟩

end M9Native.LagrangianSymplecticMatrix

end

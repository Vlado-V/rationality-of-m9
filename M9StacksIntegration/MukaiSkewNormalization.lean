module

public import M9StacksIntegration.LagrangianSymplecticMatrix

/-!
# Normalizing an actual nondegenerate skew bivector from an isotropic quotient

A right inverse of a surjective isotropic quotient supplies one half of
the basis. The bivector supplies the partner columns, and its inverse
form gives an explicit triangular correction. No symplectic-basis or
normal-form conclusion is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix

namespace M9Native.MukaiSkewNormalization

variable {k n : Type*} [Field k] [CharZero k]
  [Fintype n] [DecidableEq n] [LinearOrder n]

abbrev I := n ⊕ n

def gram (B : Matrix (I (n := n)) (I (n := n)) k)
    (S : Matrix (I (n := n)) n k) : Matrix n n k := Sᵀ * B⁻¹ * S

omit [CharZero k] [LinearOrder n] in
theorem inverse_skew (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) : B⁻¹ᵀ = -B⁻¹ := by
  have ht : B⁻¹ᵀ * (-B) = 1 := by
    simpa only [Matrix.transpose_mul, hskew, Matrix.transpose_one] using
      congrArg Matrix.transpose (B.mul_nonsing_inv hB)
  have hc : B⁻¹ᵀ * B = -1 := by
    apply neg_injective
    simpa only [Matrix.mul_neg, neg_neg] using ht
  calc
    _ = (B⁻¹ᵀ * B) * B⁻¹ := (B.mul_nonsing_inv_cancel_right B⁻¹ᵀ hB).symm
    _ = _ := by rw [hc]; simp

omit [CharZero k] [LinearOrder n] in
theorem gram_skew (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (S : Matrix (I (n := n)) n k) :
    (gram B S)ᵀ = -gram B S := by
  simp [gram, Matrix.transpose_mul, inverse_skew B hB hskew, Matrix.mul_assoc]

omit [LinearOrder n] in
theorem gram_diag (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (S : Matrix (I (n := n)) n k) (i : n) :
    gram B S i i = 0 := by
  have h := congrFun (congrFun (gram_skew B hB hskew S) i) i
  change gram B S i i = -gram B S i i at h
  have hz : (2 : k) * gram B S i i = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

def partner (B : Matrix (I (n := n)) (I (n := n)) k)
    (M : Matrix n (I (n := n)) k) : Matrix (I (n := n)) n k := -B * Mᵀ

omit [CharZero k] [LinearOrder n] in
theorem section_partner (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (M : Matrix n (I (n := n)) k)
    (S : Matrix (I (n := n)) n k) (hMS : M * S = 1) :
    Sᵀ * B⁻¹ * partner B M = -1 := by
  calc
    _ = -(Sᵀ * (B⁻¹ * B) * Mᵀ) := by simp [partner, Matrix.mul_assoc]
    _ = -(M * S)ᵀ := by rw [B.nonsing_inv_mul hB, Matrix.mul_one, Matrix.transpose_mul]
    _ = _ := by rw [hMS, Matrix.transpose_one]

omit [CharZero k] [DecidableEq n] [LinearOrder n] in
theorem partner_transpose (B : Matrix (I (n := n)) (I (n := n)) k)
    (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k) :
    (partner B M)ᵀ = M * B := by
  simp [partner, Matrix.transpose_mul, hskew]

omit [CharZero k] [LinearOrder n] in
theorem partner_section (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k)
    (S : Matrix (I (n := n)) n k) (hMS : M * S = 1) :
    (partner B M)ᵀ * B⁻¹ * S = 1 := by
  rw [partner_transpose B hskew]
  calc
    _ = M * (B * B⁻¹) * S := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [B.mul_nonsing_inv hB, Matrix.mul_one, hMS]

omit [CharZero k] [LinearOrder n] in
theorem partner_isotropic (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k)
    (hiso : M * B * Mᵀ = 0) : gram B (partner B M) = 0 := by
  unfold gram
  rw [partner_transpose B hskew]
  calc
    _ = -(M * (B * B⁻¹) * B * Mᵀ) := by simp [partner, Matrix.mul_assoc]
    _ = _ := by rw [B.mul_nonsing_inv hB, Matrix.mul_one, hiso, neg_zero]

def correctedSection (B : Matrix (I (n := n)) (I (n := n)) k)
    (M : Matrix n (I (n := n)) k) (S : Matrix (I (n := n)) n k) :
    Matrix (I (n := n)) n k :=
  S + partner B M * LagrangianSymplecticMatrix.upperPart (gram B S)

omit [CharZero k] [LinearOrder n] in
theorem gram_add_partner (B : Matrix (I (n := n)) (I (n := n)) k)
    (S C : Matrix (I (n := n)) n k) (T : Matrix n n k) :
    gram B (S + C * T) = gram B S + (Sᵀ * B⁻¹ * C) * T +
      Tᵀ * (Cᵀ * B⁻¹ * S) + Tᵀ * gram B C * T := by
  simp only [gram, Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc]
  abel

theorem correctedSection_isotropic (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k)
    (S : Matrix (I (n := n)) n k) (hMS : M * S = 1) (hiso : M * B * Mᵀ = 0) :
    gram B (correctedSection B M S) = 0 := by
  rw [correctedSection, gram_add_partner, section_partner B hB M S hMS,
    partner_section B hB hskew M S hMS, partner_isotropic B hB hskew M hiso]
  simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero]
  have h := LagrangianSymplecticMatrix.upperPart_sub_transpose (gram B S)
    (gram_skew B hB hskew S) (gram_diag B hB hskew S)
  calc
    _ = (LagrangianSymplecticMatrix.upperPart (gram B S) -
        (LagrangianSymplecticMatrix.upperPart (gram B S))ᵀ) +
        -LagrangianSymplecticMatrix.upperPart (gram B S) +
        (LagrangianSymplecticMatrix.upperPart (gram B S))ᵀ := by rw [h]
    _ = 0 := by abel

omit [CharZero k] in
theorem correctedSection_partner (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k)
    (S : Matrix (I (n := n)) n k) (hMS : M * S = 1) (hiso : M * B * Mᵀ = 0) :
    (correctedSection B M S)ᵀ * B⁻¹ * partner B M = -1 := by
  calc
    _ = Sᵀ * B⁻¹ * partner B M +
        (LagrangianSymplecticMatrix.upperPart (gram B S))ᵀ * gram B (partner B M) := by
      simp [correctedSection, gram, Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.add_mul, Matrix.mul_assoc]
    _ = _ := by rw [section_partner B hB M S hMS, partner_isotropic B hB hskew M hiso]; simp

omit [CharZero k] in
theorem partner_correctedSection (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k)
    (S : Matrix (I (n := n)) n k) (hMS : M * S = 1) (hiso : M * B * Mᵀ = 0) :
    (partner B M)ᵀ * B⁻¹ * correctedSection B M S = 1 := by
  calc
    _ = (partner B M)ᵀ * B⁻¹ * S + gram B (partner B M) *
        LagrangianSymplecticMatrix.upperPart (gram B S) := by
      simp [correctedSection, gram, Matrix.mul_add, Matrix.mul_assoc]
    _ = _ := by rw [partner_section B hB hskew M S hMS,
      partner_isotropic B hB hskew M hiso]; simp

def normalization (B : Matrix (I (n := n)) (I (n := n)) k)
    (M : Matrix n (I (n := n)) k) (S : Matrix (I (n := n)) n k) :
    Matrix (I (n := n)) (I (n := n)) k :=
  Matrix.fromCols (correctedSection B M S) (partner B M)

theorem normalization_gram (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : IsUnit B.det) (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k)
    (S : Matrix (I (n := n)) n k) (hMS : M * S = 1) (hiso : M * B * Mᵀ = 0) :
    (normalization B M S)ᵀ * B⁻¹ * normalization B M S = Matrix.J n k := by
  unfold normalization
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  change Matrix.fromBlocks (gram B (correctedSection B M S))
    ((correctedSection B M S)ᵀ * B⁻¹ * partner B M)
    ((partner B M)ᵀ * B⁻¹ * correctedSection B M S) (gram B (partner B M)) = _
  rw [correctedSection_isotropic B hB hskew M S hMS hiso,
    correctedSection_partner B hB hskew M S hMS hiso,
    partner_correctedSection B hB hskew M S hMS hiso,
    partner_isotropic B hB hskew M hiso]
  rfl

/-- A surjective isotropic quotient constructs a genuine change of
basis taking the fixed standard bivector to the given skew matrix. -/
theorem exists_normalization (B : Matrix (I (n := n)) (I (n := n)) k)
    (hB : B.det ≠ 0) (hskew : Bᵀ = -B) (M : Matrix n (I (n := n)) k)
    (hsurj : Function.Surjective M.mulVec) (hiso : M * B * Mᵀ = 0) :
    ∃ P : Matrix (I (n := n)) (I (n := n)) k,
      IsUnit P ∧ P * (-Matrix.J n k) * Pᵀ = B := by
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  obtain ⟨S, hS⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
  let P := normalization B M S
  have hgram : Pᵀ * B⁻¹ * P = Matrix.J n k := normalization_gram B hBu hskew M S hS hiso
  have hPdet : P.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hgram
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, zero_mul] at h
    exact (Matrix.isUnit_det_J n k).ne_zero h.symm
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  have hc : P * (-Matrix.J n k) * Pᵀ * B⁻¹ = 1 := by
    apply Matrix.mul_left_injective_of_inv P P⁻¹ (P.mul_nonsing_inv hPu)
    calc
      _ = P * (-Matrix.J n k) * (Pᵀ * B⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgram, Matrix.mul_assoc, Matrix.neg_mul, Matrix.J_squared]; simp
  refine ⟨P, (Matrix.isUnit_iff_isUnit_det P).mpr hPu, ?_⟩
  calc
    _ = (P * (-Matrix.J n k) * Pᵀ) * (B⁻¹ * B) := by rw [B.nonsing_inv_mul hBu]; simp
    _ = _ := by rw [← Matrix.mul_assoc, hc, Matrix.one_mul]

end M9Native.MukaiSkewNormalization

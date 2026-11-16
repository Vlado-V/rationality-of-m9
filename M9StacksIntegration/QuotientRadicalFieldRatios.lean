module

public import M9StacksIntegration.FiveAlternatingCofactors
public import M9.RadicalFiber

/-! Actual cofactor descent of the radical ratios of a split five-by-fourteen quotient.
This is a field-of-definition statement for literal matrices and their intrinsic radical. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix Module
open scoped BigOperators

namespace M9Native.QuotientRadicalFieldRatios

open MatrixChartFieldRecovery

variable {K : Type*} [Field K]

def annihilatorLift (J : Matrix (Fin 14) (Fin 14) K) (N : Matrix (Fin 5) (Fin 14) K) :
    Matrix (Fin 14) (Fin 5) K := J⁻¹*Nᵀ

def annihilatorGram (J : Matrix (Fin 14) (Fin 14) K) (N : Matrix (Fin 5) (Fin 14) K) :
    Matrix (Fin 5) (Fin 5) K := N*annihilatorLift J N

theorem pairing_mul_lift (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (N : Matrix (Fin 5) (Fin 14) K) : J*annihilatorLift J N = Nᵀ := by
  rw [annihilatorLift, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul]

theorem lift_left_inverse (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (N : Matrix (Fin 5) (Fin 14) K) (S : Matrix (Fin 14) (Fin 5) K) (hNS : N*S = 1) :
    (Sᵀ*J)*annihilatorLift J N = 1 := by
  rw [Matrix.mul_assoc, pairing_mul_lift J hJ N, ← Matrix.transpose_mul, hNS,
    Matrix.transpose_one]

theorem lift_mem_radical (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (hAlt : (Matrix.toBilin' J).IsAlt) (N : Matrix (Fin 5) (Fin 14) K)
    (x : Fin 5 → K) (hx : annihilatorGram J N *ᵥ x = 0) :
    annihilatorLift J N *ᵥ x ∈
      M9.RadicalFiber.radical (Matrix.toBilin' J) (LinearMap.ker N.mulVecLin) := by
  apply (M9.RadicalFiber.mem_radical_iff (Matrix.toBilin' J) hAlt.isRefl _ _).mpr
  constructor
  · change N *ᵥ (annihilatorLift J N *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec]
    exact hx
  · intro y hy
    apply hAlt.isRefl
    rw [Matrix.toBilin'_apply']
    change y ⬝ᵥ (J *ᵥ (annihilatorLift J N *ᵥ x)) = 0
    rw [Matrix.mulVec_mulVec, pairing_mul_lift J hJ N, Matrix.dotProduct_transpose_mulVec]
    change N *ᵥ y = 0 at hy
    rw [hy, dotProduct_zero]

theorem radical_vector_recovery (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (hAlt : (Matrix.toBilin' J).IsAlt) (N : Matrix (Fin 5) (Fin 14) K)
    (S : Matrix (Fin 14) (Fin 5) K) (hNS : N*S = 1) (w : Fin 14 → K)
    (hw : w ∈ M9.RadicalFiber.radical (Matrix.toBilin' J) (LinearMap.ker N.mulVecLin)) :
    annihilatorLift J N *ᵥ (Sᵀ *ᵥ (J *ᵥ w)) = w := by
  obtain ⟨hwN, hwOrth⟩ := (M9.RadicalFiber.mem_radical_iff
    (Matrix.toBilin' J) hAlt.isRefl _ _).mp hw
  have he : J *ᵥ w = Nᵀ *ᵥ (Sᵀ *ᵥ (J *ᵥ w)) := by
    funext i
    have hz : N *ᵥ (Pi.single i 1 - S *ᵥ (N *ᵥ Pi.single i 1)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hNS, Matrix.one_mulVec, sub_self]
    have h := hAlt.isRefl _ _ (hwOrth _ hz)
    rw [Matrix.toBilin'_apply'] at h
    change (Pi.single i 1 - S *ᵥ (N *ᵥ Pi.single i 1)) ⬝ᵥ (J *ᵥ w) = 0 at h
    rw [sub_dotProduct] at h
    have hv := sub_eq_zero.mp h
    have hs : (S *ᵥ (N *ᵥ Pi.single i 1)) ⬝ᵥ (J *ᵥ w) =
        Pi.single i 1 ⬝ᵥ (Nᵀ *ᵥ (Sᵀ *ᵥ (J *ᵥ w))) := by
      calc
        _ = (J *ᵥ w) ⬝ᵥ (S *ᵥ (N *ᵥ Pi.single i 1)) := dotProduct_comm _ _
        _ = (N *ᵥ Pi.single i 1) ⬝ᵥ (Sᵀ *ᵥ (J *ᵥ w)) :=
          (Matrix.dotProduct_transpose_mulVec S _ _).symm
        _ = (Sᵀ *ᵥ (J *ᵥ w)) ⬝ᵥ (N *ᵥ Pi.single i 1) := dotProduct_comm _ _
        _ = _ := (Matrix.dotProduct_transpose_mulVec N _ _).symm
    have hh := hv.trans hs
    simpa [dotProduct, Pi.single_apply] using hh
  rw [annihilatorLift, ← Matrix.mulVec_mulVec, ← he, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec]

theorem map_kernel_eq_radical (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (hAlt : (Matrix.toBilin' J).IsAlt) (N : Matrix (Fin 5) (Fin 14) K)
    (S : Matrix (Fin 14) (Fin 5) K) (hNS : N*S = 1) :
    (LinearMap.ker (annihilatorGram J N).mulVecLin).map (annihilatorLift J N).mulVecLin =
      M9.RadicalFiber.radical (Matrix.toBilin' J) (LinearMap.ker N.mulVecLin) := by
  apply le_antisymm
  · rintro w ⟨x, hx, rfl⟩
    exact lift_mem_radical J hJ hAlt N x hx
  · intro w hw
    let x := Sᵀ *ᵥ (J *ᵥ w)
    have hxw : annihilatorLift J N *ᵥ x = w := radical_vector_recovery J hJ hAlt N S hNS w hw
    refine ⟨x, ?_, hxw⟩
    change (N * annihilatorLift J N) *ᵥ x = 0
    rw [← Matrix.mulVec_mulVec, hxw]
    exact hw.1

theorem gram_rank_of_radical_one (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (hAlt : (Matrix.toBilin' J).IsAlt) (N : Matrix (Fin 5) (Fin 14) K)
    (S : Matrix (Fin 14) (Fin 5) K) (hNS : N*S = 1)
    (hdim : Module.finrank K
      (M9.RadicalFiber.radical (Matrix.toBilin' J) (LinearMap.ker N.mulVecLin)) = 1) :
    (annihilatorGram J N).rank = 4 := by
  have hinj : Function.Injective (annihilatorLift J N).mulVecLin := by
    intro x y hxy
    have h := congrArg (fun v : Fin 14 → K => (Sᵀ*J) *ᵥ v) hxy
    simp only [Matrix.mulVecLin_apply] at h
    simpa only [Matrix.mulVec_mulVec, lift_left_inverse J hJ N S hNS,
      Matrix.one_mulVec] using h
  have hdimKer := (Submodule.equivMapOfInjective (annihilatorLift J N).mulVecLin hinj
    (LinearMap.ker (annihilatorGram J N).mulVecLin)).finrank_eq
  rw [map_kernel_eq_radical J hJ hAlt N S hNS, hdim] at hdimKer
  have h := (annihilatorGram J N).mulVecLin.finrank_range_add_finrank_ker
  change (annihilatorGram J N).rank +
    Module.finrank K (LinearMap.ker (annihilatorGram J N).mulVecLin) =
      Module.finrank K (Fin 5 → K) at h
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  omega

theorem lift_kernelVector_ne_zero (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (N : Matrix (Fin 5) (Fin 14) K) (S : Matrix (Fin 14) (Fin 5) K) (hNS : N*S = 1)
    (i j : Fin 5) (hij : (annihilatorGram J N).adjugate i j ≠ 0) :
    annihilatorLift J N *ᵥ FiveAlternatingCofactors.kernelVector (annihilatorGram J N) j ≠ 0 := by
  intro h
  have he := congrArg (fun v : Fin 14 → K => (Sᵀ*J) *ᵥ v) h
  rw [Matrix.mulVec_mulVec, lift_left_inverse J hJ N S hNS, Matrix.one_mulVec,
    Matrix.mulVec_zero] at he
  exact FiveAlternatingCofactors.kernelVector_ne_zero _ i j hij he

theorem lift_kernelVector_mem_radical (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det)
    (hAlt : (Matrix.toBilin' J).IsAlt) (N : Matrix (Fin 5) (Fin 14) K)
    (hd : (annihilatorGram J N).det = 0) (j : Fin 5) :
    annihilatorLift J N *ᵥ FiveAlternatingCofactors.kernelVector (annihilatorGram J N) j ∈
      M9.RadicalFiber.radical (Matrix.toBilin' J) (LinearMap.ker N.mulVecLin) := by
  exact lift_mem_radical J hJ hAlt N _
    (FiveAlternatingCofactors.mulVec_kernelVector (annihilatorGram J N) hd j)

theorem lift_kernelVector_entries (E : Subfield K)
    (J : Matrix (Fin 14) (Fin 14) K) (N : Matrix (Fin 5) (Fin 14) K)
    (hJE : EntriesIn E J) (hNE : EntriesIn E N) (j : Fin 5) :
    ∀ i, (annihilatorLift J N *ᵥ
      FiveAlternatingCofactors.kernelVector (annihilatorGram J N) j) i ∈ E := by
  have hT : EntriesIn E (annihilatorLift J N) := (hJE.inv E).mul E (hNE.transpose E)
  have hG : EntriesIn E (annihilatorGram J N) := hNE.mul E hT
  intro i
  change (∑ k : Fin 5, annihilatorLift J N i k *
    FiveAlternatingCofactors.kernelVector (annihilatorGram J N) j k) ∈ E
  apply E.sum_mem
  intro k _
  exact E.mul_mem (hT i k) (FiveAlternatingCofactors.kernelVector_mem E _ hG j k)

/-- A representative of a one-dimensional radical with coefficients in E determines
the normalized ratios of every other representative over E. -/
theorem ratios_mem_of_span (E : Subfield K) (w w₀ α : Fin 14 → K)
    (β : Matrix (Fin 13) (Fin 14) K) (hw : w ≠ 0)
    (hspan : w ∈ Submodule.span K {w₀}) (hwE : ∀ i, w i ∈ E)
    (hαE : ∀ i, α i ∈ E) (hβE : EntriesIn E β) (hα : α ⬝ᵥ w₀ ≠ 0) :
    ∀ j, (β j ⬝ᵥ w₀) / (α ⬝ᵥ w₀) ∈ E := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hc0 : c ≠ 0 := by
    intro hz
    apply hw
    rw [← hc, hz, zero_smul]
  have hden : α ⬝ᵥ w ∈ E := E.sum_mem (fun i _ => E.mul_mem (hαE i) (hwE i))
  intro j
  have hnum : β j ⬝ᵥ w ∈ E := E.sum_mem (fun i _ => E.mul_mem (hβE j i) (hwE i))
  have heq : (β j ⬝ᵥ w₀) / (α ⬝ᵥ w₀) = (β j ⬝ᵥ w) / (α ⬝ᵥ w) := by
    rw [← hc, dotProduct_smul, dotProduct_smul]
    change (β j ⬝ᵥ w₀) / (α ⬝ᵥ w₀) =
      (c*(β j ⬝ᵥ w₀)) / (c*(α ⬝ᵥ w₀))
    field_simp [hc0, hα]
  rw [heq]
  exact E.div_mem hnum hden

/-- The normalized radical coordinates are derived from actual polynomial cofactors
of the annihilator Gram matrix, with no field-of-definition assumption on the radical line. -/
theorem radical_ratios_mem (E : Subfield K)
    (J : Matrix (Fin 14) (Fin 14) K) (hJ : IsUnit J.det) (hAlt : (Matrix.toBilin' J).IsAlt)
    (N : Matrix (Fin 5) (Fin 14) K) (S : Matrix (Fin 14) (Fin 5) K) (hNS : N*S = 1)
    (hJE : EntriesIn E J) (hNE : EntriesIn E N)
    (w₀ α : Fin 14 → K) (β : Matrix (Fin 13) (Fin 14) K)
    (hRad : M9.RadicalFiber.radical (Matrix.toBilin' J) (LinearMap.ker N.mulVecLin) =
      Submodule.span K {w₀})
    (hαE : ∀ i, α i ∈ E) (hβE : EntriesIn E β) (hα : α ⬝ᵥ w₀ ≠ 0) :
    ∀ j, (β j ⬝ᵥ w₀) / (α ⬝ᵥ w₀) ∈ E := by
  have hw₀ : w₀ ≠ 0 := by
    intro hz
    exact hα (by rw [hz, dotProduct_zero])
  have hdim : Module.finrank K
      (M9.RadicalFiber.radical (Matrix.toBilin' J) (LinearMap.ker N.mulVecLin)) = 1 := by
    rw [hRad]
    exact finrank_span_singleton hw₀
  have hr := gram_rank_of_radical_one J hJ hAlt N S hNS hdim
  have hd : (annihilatorGram J N).det = 0 := by
    by_contra h
    have he := Matrix.rank_of_det_ne_zero h
    rw [hr] at he
    norm_num at he
  obtain ⟨i, j, hij⟩ := FiveAlternatingCofactors.exists_nonzero_cofactor_of_rank_four _ hr
  apply ratios_mem_of_span E
    (annihilatorLift J N *ᵥ FiveAlternatingCofactors.kernelVector (annihilatorGram J N) j)
    w₀ α β
  · exact lift_kernelVector_ne_zero J hJ N S hNS i j hij
  · rw [← hRad]
    exact lift_kernelVector_mem_radical J hJ hAlt N hd j
  · exact lift_kernelVector_entries E J N hJE hNE j
  · exact hαE
  · exact hβE
  · exact hα

end M9Native.QuotientRadicalFieldRatios

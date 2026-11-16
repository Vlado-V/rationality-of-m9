module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic

/-! A selected pair in an actual generating triple of a rank-two free
module has unit entry ideal. On the exact determinant-zero ring a unit
entry gives the literal rank-one kernel, over arbitrary coefficient
rings, including rings with nilpotents. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators

universe u v
namespace M9Native.RankTwoSelectedPairAlgebra

variable (R : Type u) [CommRing R]

def selectedEntries (M : Matrix (Fin 2) (Fin 3) R) (e : Fin 2 ↪ Fin 3) : Ideal R :=
  Ideal.span (Set.range fun ij : Fin 2 × Fin 2 => M ij.1 (e ij.2))

theorem selected_entry_mem (M : Matrix (Fin 2) (Fin 3) R) (e : Fin 2 ↪ Fin 3)
    (i j : Fin 2) : M i (e j) ∈ selectedEntries R M e :=
  Ideal.subset_span ⟨(i,j), rfl⟩

/-- Two of the three generating columns cannot vanish simultaneously
over any nonzero quotient ring. This is an ideal identity, not a test
on residue-field ranks. -/
theorem selectedEntries_eq_top (M : Matrix (Fin 2) (Fin 3) R)
    (hM : Function.Surjective M.mulVec) (e : Fin 2 ↪ Fin 3) :
    selectedEntries R M e = ⊤ := by
  classical
  obtain ⟨N, hN⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hM
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  let q := Ideal.Quotient.mk (selectedEntries R M e)
  have hq (i j : Fin 2) : q (M i (e j)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (selected_entry_mem R M e i j)
  have h00 := hq 0 0
  have h01 := hq 0 1
  have h10 := hq 1 0
  have h11 := hq 1 1
  have hdet : q (M * N).det = 1 := by rw [hN, Matrix.det_one, map_one]
  simp only [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_three, map_sub, map_add, map_mul] at hdet
  have he : e 0 ≠ e 1 := fun h => Fin.zero_ne_one (e.injective h)
  have he0 : e 0 = 0 ∨ e 0 = 1 ∨ e 0 = 2 := by omega
  have he1 : e 1 = 0 ∨ e 1 = 1 ∨ e 1 = 2 := by omega
  rcases he0 with ha | ha | ha <;> rcases he1 with hb | hb | hb
  all_goals
    first
    | exact (he (ha.trans hb.symm)).elim
    | rw [ha] at h00 h10
      rw [hb] at h01 h11
      simp only [h00, h01, h10, h11, zero_mul, zero_add, add_zero] at hdet
      have hz : (0 : R ⧸ selectedEntries R M e) = 1 := by
        calc
          _ = _ := by ring
          _ = 1 := hdet
      exact hz.symm

/-- The literal same pair remains unimodular after every ring map. -/
theorem selectedEntries_map_eq_top {S : Type v} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 2) (Fin 3) R) (hM : Function.Surjective M.mulVec)
    (e : Fin 2 ↪ Fin 3) :
    Ideal.span (Set.range fun ij : Fin 2 × Fin 2 => f (M ij.1 (e ij.2))) = ⊤ := by
  change Ideal.span (Set.range (f ∘ fun ij : Fin 2 × Fin 2 => M ij.1 (e ij.2))) = ⊤
  rw [Set.range_comp, ← Ideal.map_span]
  change (selectedEntries R M e).map f = ⊤
  rw [selectedEntries_eq_top R M hM e, Ideal.map_top]

section UnitPivot

variable (a : Rˣ) (b c d : R) (hdet : (a : R) * d - b * c = 0)

include hdet in
theorem lowerRight_eq : d = c * (↑a⁻¹ : R) * b := by
  calc
    d = (↑a⁻¹ : R) * ((a : R) * d) := by simp [← mul_assoc]
    _ = (↑a⁻¹ : R) * (b * c) := by rw [sub_eq_zero.mp hdet]
    _ = _ := by ring

include hdet in
/-- The actual two equations are equivalent to one literal linear
equation, without passing to a reduced ring. -/
theorem unitPivot_kernel_iff (v : Fin 2 → R) :
    (!![(a : R), b; c, d] *ᵥ v = 0) ↔
      v 0 = -(↑a⁻¹ : R) * b * v 1 := by
  constructor
  · intro h
    have h0 : (a : R) * v 0 + b * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
    calc
      v 0 = (↑a⁻¹ : R) * ((a : R) * v 0) := by simp [← mul_assoc]
      _ = (↑a⁻¹ : R) * (-(b * v 1)) := by rw [eq_neg_of_add_eq_zero_left h0]
      _ = _ := by ring
  · intro h
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h, ← mul_assoc]
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply]
      rw [lowerRight_eq R a b c d hdet, h]
      ring

include hdet in
theorem kernel_vector (z : R) :
    !![(a : R), b; c, d] *ᵥ ![-(↑a⁻¹ : R) * b * z, z] = 0 :=
  (unitPivot_kernel_iff R a b c d hdet _).mpr rfl

include hdet in
/-- A generating projective coordinate pair in this actual kernel has
a unit second coordinate, so lies in the genuine second affine chart. -/
theorem unit_second_coordinate (v : Fin 2 → R)
    (hv : Ideal.span (Set.range v) = ⊤)
    (hk : !![(a : R), b; c, d] *ᵥ v = 0) : IsUnit (v 1) := by
  apply Ideal.span_singleton_eq_top.mp
  apply top_unique
  rw [← hv]
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · change v 0 ∈ _
    rw [(unitPivot_kernel_iff R a b c d hdet v).mp hk]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · change v 1 ∈ _
    exact Ideal.subset_span (Set.mem_singleton _)

end UnitPivot
end M9Native.RankTwoSelectedPairAlgebra

module

public import M9StacksIntegration.MukaiQuarticBlockSigns

/-! Scalar bilinear components of the genuine exterior operator. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiQuarticComponents

open LagrangianField MukaiQuarticHitchin MukaiQuarticCubic
open MukaiQuarticCoordinates MukaiQuarticBlockVolume MukaiQuarticBlockSigns

variable (K : Type*) [Field K]

def entry (i j : Fin 6) : Module.End K (DualSix K) →ₗ[K] K where
  toFun A := A (LinearMap.proj j) (basisVector K i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem entry_apply (A : Module.End K (DualSix K)) (i j : Fin 6) :
    entry K i j A = A (LinearMap.proj j) (basisVector K i) := rfl

def component (i j : Fin 6) : Three K →ₗ[K] Three K →ₗ[K] K :=
  (mixedOperator K).compr₂ (entry K i j)

theorem component_basis (a b c d e f i j : Fin 6) :
    component K i j (wedge3 K (basisVector K a) (basisVector K b) (basisVector K c))
      (wedge3 K (basisVector K d) (basisVector K e) (basisVector K f)) =
      (if j = a then 1 else 0) * signature K ![i,b,c,d,e,f] -
      (if j = b then 1 else 0) * signature K ![i,a,c,d,e,f] +
      (if j = c then 1 else 0) * signature K ![i,a,b,d,e,f] :=
  mixedOperator_basis K a b c d e f i j

theorem entry_hitchin_component (w : Three K) (i j : Fin 6) :
    entry K i j (hitchinOperator K w) = component K i j w w := rfl

theorem entry_polar_component (u v : Three K) (i j : Fin 6) :
    entry K i j (polarOperator K u v) = component K i j u v + component K i j v u := rfl

theorem e_ne_f (i j : Fin 3) : eIndex i ≠ fIndex j := by
  intro h
  have hv := congrArg Fin.val h
  simp [eIndex, fIndex] at hv
  have hi := i.isLt
  omega

theorem f_ne_e (i j : Fin 3) : fIndex i ≠ eIndex j := (e_ne_f j i).symm

theorem e_eq_e (i j : Fin 3) : (eIndex i = eIndex j) ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa [eIndex] using hv
  · rintro rfl
    rfl

theorem f_eq_f (i j : Fin 3) : (fIndex i = fIndex j) ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [fIndex] at hv
    omega
  · rintro rfl
    rfl

theorem component_qq_first (i : Fin 6) (j a b c d : Fin 3) :
    component K i (eIndex j) (q K a b) (q K c d) = 0 := by
  simp only [q, e, f]
  rw [component_basis, signature_F1245 K i (eIndex c)
    (nextOne b) (nextTwo b) (nextOne d) (nextTwo d)]
  simp [e_ne_f]

theorem component_qb_first (i : Fin 6) (j a b : Fin 3) :
    component K i (eIndex j) (q K a b) (LagrangianField.b K) = 0 := by
  simp only [q, LagrangianField.b, e, f]
  rw [component_basis, signature_F1245 K i (fIndex 0) (nextOne b) (nextTwo b) 1 2]
  simp [e_ne_f]

theorem component_b_first (v : Three K) (i : Fin 6) (j : Fin 3) :
    component K i (eIndex j) (b K) v = 0 := by
  change mixedOperator K (b K) v (LinearMap.proj (eIndex j)) (basisVector K i) = 0
  rw [mixedOperator_apply, mixedTop, b, wedge3, MukaiQuarticExterior.interior_ιMulti]
  have hf (a : Fin 3) :
      (LinearMap.proj (eIndex j) : V K →ₗ[K] K) (f K a) = 0 := by
    simp [LinearMap.proj_apply, f, basisVector, e_ne_f]
  simp [hf]

theorem component_qq_last (i j a b c d : Fin 3) :
    component K (fIndex i) (fIndex j) (q K a b) (q K c d) = 0 := by
  simp only [q, e, f]
  rw [component_basis]
  simp only [signature_F0245, mul_zero, sub_zero, add_zero]

theorem component_qb_last (i j a b : Fin 3) :
    component K (fIndex i) (fIndex j) (q K a b) (LagrangianField.b K) = 0 := by
  simp only [q, LagrangianField.b, e, f]
  rw [component_basis]
  simp only [signature_F0245, mul_zero, sub_zero, add_zero]

theorem component_bq_last (i j c d : Fin 3) :
    component K (fIndex i) (fIndex j) (b K) (q K c d) = 0 := by
  simp only [q, b, e, f]
  rw [component_basis]
  simp only [signature_F0245, mul_zero, sub_zero, add_zero]

theorem component_bb_last (i j : Fin 3) :
    component K (fIndex i) (fIndex j) (b K) (b K) = 0 := by
  simp only [b, f]
  rw [component_basis]
  simp only [signature_F0245, mul_zero, sub_zero, add_zero]

theorem component_bq_cross (i j c d : Fin 3) :
    component K (eIndex i) (fIndex j) (b K) (q K c d) = 0 := by
  simp only [q, b, e, f]
  rw [component_basis]
  simp only [signature_F1245, mul_zero, sub_zero, add_zero]

theorem component_bb_cross (i j : Fin 3) :
    component K (eIndex i) (fIndex j) (b K) (b K) = 0 := by
  simp only [b, f]
  rw [component_basis]
  simp only [signature_F1245, mul_zero, sub_zero, add_zero]

theorem component_qb_cross (i j a b : Fin 3) :
    component K (eIndex i) (fIndex j) (q K a b) (LagrangianField.b K) = 0 := by
  simp only [q, LagrangianField.b, e, f]
  rw [component_basis]
  simp only [signature_F2345, mul_zero, sub_zero, add_zero]

theorem component_qq_cross (i j a b c d : Fin 3) :
    component K (eIndex i) (fIndex j) (q K a b) (q K c d) =
      epsilon K i a c * epsilon K b j d := by
  simp only [q, e, f]
  rw [component_basis, signature_F1245 K (eIndex i) (eIndex c)
    (nextOne b) (nextTwo b) (nextOne d) (nextTwo d)]
  rw [signature_eefeff, signature_eefeff]
  simp only [epsilon_missing, f_eq_f, mul_zero, zero_sub]
  rw [← epsilon_interior K b j d]
  ring

theorem component_qa_lower (i j a b : Fin 3) :
    component K (fIndex i) (eIndex j) (q K a b) (LagrangianField.a K) =
      -(if j = a then 1 else 0) * (if i = b then 1 else 0) := by
  simp only [q, LagrangianField.a, e, f]
  rw [component_basis, signature_fffeee K 0 1 2 i (nextOne b) (nextTwo b),
    epsilon_missing K i b]
  simp only [e_eq_e, e_ne_f, ite_false, zero_mul, sub_zero, add_zero]
  norm_num [epsilon, blockMatrix, Matrix.det_fin_three]
  split_ifs <;> ring

theorem component_aq_lower (i j c d : Fin 3) :
    component K (fIndex i) (eIndex j) (a K) (q K c d) =
      -(if j = c then 1 else 0) * (if i = d then 1 else 0) := by
  simp only [a, q, e, f]
  rw [component_basis, signature_feeeff, signature_feeeff, signature_feeeff]
  simp only [epsilon_missing K i d, e_eq_e]
  fin_cases j <;> fin_cases c <;>
    norm_num [epsilon, blockMatrix, Matrix.det_fin_three] <;> (split_ifs <;> ring)

theorem component_qp_lower (i j a b c d : Fin 3) :
    component K (fIndex i) (eIndex j) (q K a b) (p K c d) = 0 := by
  simp only [q, p, e, f]
  rw [component_basis, signature_F0123 K (eIndex (nextOne d)) (eIndex (nextTwo d))
    i (nextOne b) (nextTwo b) c]
  simp [e_ne_f]

theorem component_pq_lower (i j a b c d : Fin 3) :
    component K (fIndex i) (eIndex j) (p K a b) (q K c d) = 0 := by
  simp only [q, p, e, f]
  rw [component_basis]
  simp [signature_F0145, e_ne_f]

theorem component_pb_lower (i j a b : Fin 3) :
    component K (fIndex i) (eIndex j) (p K a b) (LagrangianField.b K) = 0 := by
  simp only [p, LagrangianField.b, e, f]
  rw [component_basis]
  simp [signature_F0145, e_ne_f]

theorem component_ab_lower (i j : Fin 3) :
    component K (fIndex i) (eIndex j) (a K) (b K) = 0 := by
  simp only [a, b, e, f]
  rw [component_basis]
  simp only [signature_F0345, mul_zero, sub_zero, add_zero]

end M9Native.MukaiQuarticComponents

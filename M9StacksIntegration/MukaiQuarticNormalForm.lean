module

public import M9StacksIntegration.MukaiQuarticComponents
public import M9StacksIntegration.MukaiQuarticVariation

/-!
# The actual operator on the native origin conormal

The normal vector is the literal sum of the actual `b` and `q` exterior
wedges. Coordinate signs are computed by the proved alternating-volume
formula. No adjugate or determinant coefficient is imposed as data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

open Module Matrix
open scoped BigOperators

namespace M9Native.MukaiQuarticNormalForm

open LagrangianField MukaiConormalPrimitive MukaiPrimitiveProjector
open MukaiQuarticHitchin MukaiQuarticCubic MukaiQuarticCoordinates
open MukaiQuarticComponents MukaiQuarticBlockVolume

variable (K : Type*) [Field K]

def normal (c : K) (S : Matrix (Fin 3) (Fin 3) K) : Third K :=
  c • b K + mixedQ K S

def normalEntry (S : Matrix (Fin 3) (Fin 3) K) (i j : Fin 6) : K :=
  Fin.addCases (m := 3) (n := 3)
    (fun i : Fin 3 => Fin.addCases (m := 3) (n := 3) (fun _ : Fin 3 => 0)
      (fun j : Fin 3 => -2 * S.adjugate j i) j)
    (fun _ : Fin 3 => 0) i

theorem entry_hitchin_normal_first (c : K) (S : Matrix (Fin 3) (Fin 3) K)
    (i : Fin 6) (j : Fin 3) :
    entry K i (eIndex j) (hitchinOperator K (normal K c S)) = 0 := by
  rw [entry_hitchin_component]
  change component K i (eIndex j) (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b)
    (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b)
     = _
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  simp [component_b_first, component_qb_first, component_qq_first]

theorem entry_hitchin_normal_last (c : K) (S : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    entry K (fIndex i) (fIndex j) (hitchinOperator K (normal K c S)) = 0 := by
  rw [entry_hitchin_component]
  change component K (fIndex i) (fIndex j)
    (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b)
    (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b)
     = _
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  simp [component_bb_last, component_bq_last, component_qb_last, component_qq_last]

private theorem sum_delta_mul (a : Fin 3) (F : Fin 3 → K) :
    (∑ x : Fin 3, (if x = a then (1 : K) else 0) * F x) = F a := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem sum_delta_pair (a b : Fin 3) (F : Fin 3 → Fin 3 → K) :
    (∑ x : Fin 3, ∑ y : Fin 3,
      ((if x = a then (1 : K) else 0) * (if y = b then 1 else 0)) * F x y) = F a b := by
  calc
    _ = ∑ x : Fin 3, (if x = a then (1 : K) else 0) *
        (∑ y : Fin 3, (if y = b then 1 else 0) * F x y) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by simp only [sum_delta_mul K]

private theorem epsilon_as_deltas (i a c : Fin 3) :
    epsilon K i a c =
      (if a = nextOne i then (1 : K) else 0) * (if c = nextTwo i then 1 else 0) -
      (if a = nextTwo i then (1 : K) else 0) * (if c = nextOne i then 1 else 0) := by
  rw [← MukaiQuarticBlockSigns.epsilon_interior K i a c]
  simp only [eq_comm]

private theorem sum_epsilon_pair (i : Fin 3) (F : Fin 3 → Fin 3 → K) :
    (∑ a : Fin 3, ∑ c : Fin 3, epsilon K i a c * F a c) =
      F (nextOne i) (nextTwo i) - F (nextTwo i) (nextOne i) := by
  simp only [epsilon_as_deltas K, sub_mul, Finset.sum_sub_distrib, sum_delta_pair K]

private theorem epsilon_swap_last (a b c : Fin 3) :
    epsilon K a b c = -epsilon K a c b := by
  simp [epsilon, blockMatrix, Matrix.det_fin_three]
  ring

private theorem epsilon_rotate (a b c : Fin 3) :
    epsilon K a b c = epsilon K b c a := by
  simp [epsilon, blockMatrix, Matrix.det_fin_three]
  ring

private theorem adjugate_eq_cyclic_minor (S : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    S.adjugate j i =
      S (nextOne i) (nextOne j) * S (nextTwo i) (nextTwo j) -
      S (nextOne i) (nextTwo j) * S (nextTwo i) (nextOne j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjugate_fin_three, nextOne, nextTwo] <;> ring

/-- Contract each alternating pair before evaluating the cyclic minor. -/
private theorem epsilon_cofactor_sum (S : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (∑ a : Fin 3, ∑ b : Fin 3, S a b *
      (∑ c : Fin 3, ∑ d : Fin 3, S c d * (epsilon K i c a * epsilon K d j b))) =
        -(2 * S.adjugate j i) := by
  calc
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        epsilon K i a c * (epsilon K j b d * -(S a b * S c d)) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [epsilon_swap_last K i c a, epsilon_rotate K d j b]
      ring
    _ = ∑ a : Fin 3, ∑ c : Fin 3, epsilon K i a c *
        (∑ b : Fin 3, ∑ d : Fin 3, epsilon K j b d * -(S a b * S c d)) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact Finset.sum_comm
    _ = _ := by
      simp only [sum_epsilon_pair K, adjugate_eq_cyclic_minor K]
      ring

theorem entry_hitchin_normal_cross (c : K) (S : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    entry K (eIndex i) (fIndex j) (hitchinOperator K (normal K c S)) = -2 * S.adjugate j i := by
  rw [entry_hitchin_component]
  change component K (eIndex i) (fIndex j)
    (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b)
    (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b)
     = _
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  simp [component_bb_cross, component_bq_cross, component_qb_cross, component_qq_cross,
    smul_eq_mul]
  exact epsilon_cofactor_sum K S i j

theorem entry_hitchin_normal (c : K) (S : Matrix (Fin 3) (Fin 3) K) (i j : Fin 6) :
    entry K i j (hitchinOperator K (normal K c S)) = normalEntry K S i j := by
  refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
    · simpa only [normalEntry, Fin.addCases_left, Fin.addCases_right, eIndex, fIndex] using
        entry_hitchin_normal_first K c S (eIndex i) j
    · simpa only [normalEntry, Fin.addCases_left, Fin.addCases_right, eIndex, fIndex] using
        entry_hitchin_normal_cross K c S i j
  · refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
    · simpa only [normalEntry, Fin.addCases_left, Fin.addCases_right, eIndex, fIndex] using
        entry_hitchin_normal_first K c S (fIndex i) j
    · simpa only [normalEntry, Fin.addCases_left, Fin.addCases_right, eIndex, fIndex] using
        entry_hitchin_normal_last K c S i j

theorem entry_polar_normal_embedding (c : K) (S : Matrix (Fin 3) (Fin 3) K)
    (r : Coordinates K) (i j : Fin 3) :
    entry K (fIndex i) (eIndex j)
      (polarOperator K (normal K c S) (coordinateEmbedding K r)) =
      -2 * r.1 * S j i := by
  rw [entry_polar_component]
  change component K (fIndex i) (eIndex j)
      (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b)
      (r.1 • a K + (∑ a : Fin 3, ∑ b : Fin 3, r.2.1.val a b • q K a b) +
        (∑ a : Fin 3, ∑ b : Fin 3, r.2.2.1.val a b • p K a b) + r.2.2.2 • b K) +
    component K (fIndex i) (eIndex j)
      (r.1 • a K + (∑ a : Fin 3, ∑ b : Fin 3, r.2.1.val a b • q K a b) +
        (∑ a : Fin 3, ∑ b : Fin 3, r.2.2.1.val a b • p K a b) + r.2.2.2 • b K)
      (c • b K + ∑ a : Fin 3, ∑ b : Fin 3, S a b • q K a b) = _
  simp only [map_add, map_sum, map_smul,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  simp [component_b_first, component_qq_first, component_qb_first,
    component_qa_lower, component_aq_lower, component_qp_lower, component_pq_lower,
    component_pb_lower, component_ab_lower, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ] <;> ring

variable [CharZero K]

theorem contraction_normal (c : K) (S : Symmetric3 K) :
    contraction K (normal K c S.val) = 0 := by simp [normal]

omit [CharZero K] in
theorem primitiveClass_normal (c : K) (S : Symmetric3 K) :
    primitiveClass K (normal K c S.val) = conormalForm K (c,S) := by
  change primitiveClass K (c • b K + ∑ i : Fin 3, ∑ j : Fin 3, S.val i j • q K i j) =
    c • primitiveClass K (b K) + ∑ i : Fin 3, ∑ j : Fin 3, S.val i j • primitiveClass K (q K i j)
  simp only [map_add, map_sum, map_smul]

theorem representative_conormalForm (c : K) (S : Symmetric3 K) :
    representative K (conormalForm K (c,S)) = normal K c S.val := by
  rw [← primitiveClass_normal, representative_primitiveClass,
    projector_of_primitive K _ (contraction_normal K c S)]

end M9Native.MukaiQuarticNormalForm

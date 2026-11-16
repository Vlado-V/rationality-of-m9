module

public import M9StacksIntegration.MukaiSchubertExpansion

/-!
# The actual projected rank-one Schubert cone

The determinant-zero condition is converted into genuine decomposable
third exterior vectors using actual ternary factorization and actual
three-dimensional bivectors. No decomposability hypothesis is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

namespace M9Native.MukaiSchubertCone

open LagrangianField MukaiConormalPrimitive MukaiSchubertExpansion

variable (K : Type*) [Field K]

def symmetricProduct (a b : Fin 3 → K) : Symmetric3 K :=
  ⟨Matrix.vecMulVec a b + Matrix.vecMulVec b a, by
    ext i j
    simp [Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm, add_comm]⟩

theorem exists_cross {b : Fin 3 → K} (hb : b ≠ 0) :
    ∃ u v : Fin 3 → K, cross K u v = b := by
  let x : Fin 3 → K := ![b 2, -b 1, b 0]
  have hx : x ≠ 0 := by
    intro hz
    apply hb
    ext i
    fin_cases i
    · simpa [x] using congrFun hz 2
    · have h := congrFun hz 1
      simpa [x] using h
    · simpa [x] using congrFun hz 0
  obtain ⟨u,v,_huv,he⟩ := MukaiThreeDimensionalBivectors.exists_pair_of_coordinates_ne_zero hx
  refine ⟨u,v,?_⟩
  ext i
  fin_cases i
  · simpa [cross, MukaiThreeDimensionalBivectors.wedgeCoordinates, x] using congrFun he 2
  · have h := congrFun he 1
    change u 0 * v 2 - u 2 * v 0 = -b 1 at h
    change u 2 * v 0 - u 0 * v 2 = b 1
    linear_combination -h
  · simpa [cross, MukaiThreeDimensionalBivectors.wedgeCoordinates, x] using congrFun he 0

theorem exists_dot (b : Fin 3 → K) (hb : b ≠ 0) (c : K) :
    ∃ z : Fin 3 → K, (∑ j : Fin 3, z j * b j) = c := by
  classical
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hb
  change b j ≠ 0 at hj
  refine ⟨Pi.single j (c / b j),?_⟩
  simp [Pi.single_apply, hj]

def firstProjection : V K →ₗ[K] (Fin 3 → K) :=
  LinearMap.pi fun i => LinearMap.proj (eIndex i)

theorem firstProjection_block (a z : Fin 3 → K) :
    firstProjection K (blockVector K a z) = a := by
  ext i
  exact Fin.append_left a z i

theorem mixed_projection_rank (a z u v : Fin 3 → K) :
    Module.finrank K (Submodule.span K (Set.range (fun i : Fin 3 =>
      firstProjection K (![blockVector K a z, blockVector K 0 u, blockVector K 0 v] i)))) ≤ 1 := by
  have hle : Submodule.span K (Set.range (fun i : Fin 3 =>
      firstProjection K (![blockVector K a z, blockVector K 0 u, blockVector K 0 v] i))) ≤
      Submodule.span K {a} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i <;> simp [firstProjection_block]
  exact (Submodule.finrank_mono hle).trans (by
    simpa using (finrank_span_le_card ({a} : Set (Fin 3 → K))))

variable [CharZero K]

theorem mixed_class (a z u v : Fin 3 → K) :
    primitiveClass K (wedge3 K (blockVector K (2 • a) z)
      (blockVector K 0 u) (blockVector K 0 v)) =
      conormalForm K (∑ j : Fin 3, z j * cross K u v j,
        symmetricProduct K a (cross K u v)) := by
  ext w
  obtain ⟨r,rfl⟩ := (primitiveEquiv K).surjective w
  rw [primitiveClass_coordinates, conormalForm_coordinates]
  simp only [mixed_wedge_a, mixed_wedge_p, mixed_wedge_q, mixed_wedge_b,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  have h10 : r.2.1.val 1 0 = r.2.1.val 0 1 := congrFun (congrFun r.2.1.property 0) 1
  have h20 : r.2.1.val 2 0 = r.2.1.val 0 2 := congrFun (congrFun r.2.1.property 0) 2
  have h21 : r.2.1.val 2 1 = r.2.1.val 1 2 := congrFun (congrFun r.2.1.property 1) 2
  simp only [Fin.sum_univ_three, symmetricProduct, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, h10, h20, h21]
  ring

variable [IsAlgClosed K]

theorem exists_mixed_class (c : K) (S : Symmetric3 K) (hdet : S.val.det = 0) :
    ∃ a z u v : Fin 3 → K,
      primitiveClass K (wedge3 K (blockVector K a z)
        (blockVector K 0 u) (blockVector K 0 v)) = conormalForm K (c,S) := by
  by_cases hS : S = 0
  · subst S
    refine ⟨0, ![c,0,0], ![0,1,0], ![0,0,1], ?_⟩
    have h := mixed_class K (0 : Fin 3 → K) ![c,0,0] ![0,1,0] ![0,0,1]
    have hs : symmetricProduct K (0 : Fin 3 → K)
        (cross K ![0,1,0] ![0,0,1]) = 0 := by
      apply Subtype.ext
      simp [symmetricProduct]
    have hc : (∑ j : Fin 3, ![c,0,0] j * cross K ![0,1,0] ![0,0,1] j) = c := by
      simp [cross, Fin.sum_univ_three]
    simpa only [smul_zero, hc, hs] using h
  · obtain ⟨a,b,hab⟩ := MukaiSingularConic.exists_symmetrized_product S.val S.property hdet
    have hb : b ≠ 0 := by
      intro hb
      apply hS
      apply Subtype.ext
      simpa [hb] using hab
    obtain ⟨u,v,huv⟩ := exists_cross K hb
    obtain ⟨z,hz⟩ := exists_dot K b hb c
    refine ⟨2 • a,z,u,v,?_⟩
    rw [mixed_class, huv, hz]
    have hs : symmetricProduct K a b = S := Subtype.ext hab.symm
    rw [hs]

/-- Every nonzero discriminant-zero form is the image of an ACTUAL
independent triple with rank at most one under the standard quotient. -/
theorem exists_independent_triple_of_discriminant_zero
    (v : MukaiConormalPencil.ConormalCoordinates K) (hv : v ≠ 0)
    (hdet : v.2.val.det = 0) :
    ∃ s : Fin 3 → V K, LinearIndependent K s ∧
      primitiveClass K (exteriorPower.ιMulti K 3 s) = conormalForm K v ∧
      Module.finrank K (Submodule.span K (Set.range (fun i => firstProjection K (s i)))) ≤ 1 := by
  obtain ⟨a,z,u,w,he⟩ := exists_mixed_class K v.1 v.2 hdet
  let s : Fin 3 → V K := ![blockVector K a z, blockVector K 0 u, blockVector K 0 w]
  have hform : conormalForm K v ≠ 0 := by
    intro hz
    exact hv (MukaiConormalOrigin.conormalForm_injective K (by simpa using hz))
  refine ⟨s,?_,he,mixed_projection_rank K a z u w⟩
  by_contra hlin
  have hz := (exteriorPower.ιMulti K 3 (M := V K)).map_linearDependent s hlin
  apply hform
  rw [← he]
  change primitiveClass K (exteriorPower.ιMulti K 3 s) = 0
  rw [hz,map_zero]

end M9Native.MukaiSchubertCone

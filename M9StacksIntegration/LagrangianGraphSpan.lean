module

public import M9StacksIntegration.LagrangianPluckerFirstJet

/-! The literal symmetric-matrix graph spans the original fourteen
primitive coordinates.  This is a calculation with the actual adjugate
and determinant, before any geometric restriction theorem is used. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Matrix Module

universe u

namespace M9Native.LagrangianGraphSpan

open LagrangianField

variable (K : Type u) [Field K]

def constantVector : Coordinates K := (1,0,0,0)
def finalVector : Coordinates K := (0,0,0,1)

def quadraticInclusion : Symmetric3 K →ₗ[K] Coordinates K where
  toFun A := (0,A,0,0)
  map_add' A B := by simp
  map_smul' a A := by simp

def linearInclusion : Symmetric3 K →ₗ[K] Coordinates K where
  toFun A := (0,0,A,0)
  map_add' A B := by simp
  map_smul' a A := by simp

def symmetricOne : Symmetric3 K := ⟨1, Matrix.transpose_one⟩

def symmetricAdjugate (A : Symmetric3 K) : Symmetric3 K :=
  ⟨A.val.adjugate, by
    change A.val.adjugate.transpose = A.val.adjugate
    rw [Matrix.adjugate_transpose,A.property]⟩

/-- This is exactly the frozen native quotient `[I|A]` graph, with the
quadratic block preceding the linear block. -/
def graph (A : Symmetric3 K) : Coordinates K :=
  LagrangianPluckerFirstJet.graphPoint K ⟨A.val,A.property⟩

theorem graph_components (A : Symmetric3 K) :
    graph K A = constantVector K + quadraticInclusion K (symmetricAdjugate K A) +
      linearInclusion K A + A.val.det • finalVector K := by
  ext <;> simp [graph, LagrangianPluckerFirstJet.graphPoint,
    constantVector, finalVector, quadraticInclusion, linearInclusion, symmetricAdjugate]

theorem graph_smul_components (a : K) (A : Symmetric3 K) :
    graph K (a • A) = constantVector K +
      a^2 • quadraticInclusion K (symmetricAdjugate K A) +
      a • linearInclusion K A + (a^3 * A.val.det) • finalVector K := by
  rw [graph_components]
  have hq : symmetricAdjugate K (a • A) = a^2 • symmetricAdjugate K A := by
    apply Subtype.ext
    change (a • A.val).adjugate = a^2 • A.val.adjugate
    simpa using Matrix.adjugate_smul a A.val
  rw [hq, map_smul, map_smul]
  congr 1
  congr 1
  exact (Matrix.det_smul A.val a).trans (by simp)

/-- The elementary three-by-three adjugate identity supplies every
symmetric quadratic coordinate from actual graph adjugates. -/
theorem adjugate_one_add (A : Matrix (Fin 3) (Fin 3) K) :
    (1+A).adjugate = 1 + Matrix.trace A • (1 : Matrix (Fin 3) (Fin 3) K) -
      A + A.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace, Fin.sum_univ_succ] <;> ring

theorem symmetricAdjugate_one_add (A : Symmetric3 K) :
    symmetricAdjugate K (symmetricOne K + A) = symmetricOne K +
      Matrix.trace A.val • symmetricOne K - A + symmetricAdjugate K A := by
  apply Subtype.ext
  exact adjugate_one_add K A.val

section CharacteristicZero
variable [CharZero K]

/-- Vanishing on the actual graph forces every homogeneous block to
vanish; the coefficients are obtained from four actual scalar values. -/
theorem homogeneous_vanishing (φ : Coordinates K →ₗ[K] K)
    (hφ : ∀ A : Symmetric3 K, φ (graph K A) = 0) (A : Symmetric3 K) :
    φ (constantVector K) = 0 ∧
      φ (quadraticInclusion K (symmetricAdjugate K A)) = 0 ∧
      φ (linearInclusion K A) = 0 ∧
      A.val.det * φ (finalVector K) = 0 := by
  have h (a : K) := hφ (a • A)
  simp only [graph_smul_components, map_add, map_smul, smul_eq_mul] at h
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  norm_num at h0 h1 hm h2
  have hq2 : (2 : K) * φ (quadraticInclusion K (symmetricAdjugate K A)) = 0 := by
    linear_combination h1 + hm - 2 * h0
  have hq : φ (quadraticInclusion K (symmetricAdjugate K A)) = 0 :=
    (mul_eq_zero.mp hq2).resolve_left (by norm_num)
  have hb6 : (6 : K) * (A.val.det * φ (finalVector K)) = 0 := by
    linear_combination h2 - 3 * h1 - hm + 3 * h0
  have hb : A.val.det * φ (finalVector K) = 0 :=
    (mul_eq_zero.mp hb6).resolve_left (by norm_num)
  have hp : φ (linearInclusion K A) = 0 := by
    linear_combination h1 - h0 - hq - hb
  exact ⟨h0,hq,hp,hb⟩

/-- No nonzero linear functional on the actual fourteen-coordinate
space vanishes on all actual symmetric quotient graphs. -/
theorem linearMap_eq_zero_of_graph (φ : Coordinates K →ₗ[K] K)
    (hφ : ∀ A : Symmetric3 K, φ (graph K A) = 0) : φ = 0 := by
  have hc : φ (constantVector K) = 0 :=
    (homogeneous_vanishing K φ hφ 0).1
  have hq (A : Symmetric3 K) : φ (quadraticInclusion K (symmetricAdjugate K A)) = 0 :=
    (homogeneous_vanishing K φ hφ A).2.1
  have hp (A : Symmetric3 K) : φ (linearInclusion K A) = 0 :=
    (homogeneous_vanishing K φ hφ A).2.2.1
  have hb : φ (finalVector K) = 0 := by
    simpa [symmetricOne] using (homogeneous_vanishing K φ hφ (symmetricOne K)).2.2.2
  have hqi : φ (quadraticInclusion K (symmetricOne K)) = 0 := by
    simpa [symmetricAdjugate, symmetricOne] using hq (symmetricOne K)
  have hqa (A : Symmetric3 K) : φ (quadraticInclusion K A) = 0 := by
    have h := hq (symmetricOne K + A)
    rw [symmetricAdjugate_one_add] at h
    simp only [map_add, map_sub, map_smul, hqi, hq A, smul_eq_mul] at h
    simpa using h
  apply LinearMap.ext
  intro x
  have hx : x = x.1 • constantVector K + quadraticInclusion K x.2.1 +
      linearInclusion K x.2.2.1 + x.2.2.2 • finalVector K := by
    ext <;> simp [constantVector, finalVector, quadraticInclusion, linearInclusion]
  rw [hx, map_add, map_add, map_add, map_smul, map_smul, hc, hqa, hp, hb]
  simp

/-- The original fixed fourteen-coordinate function family has no
linear relation on the actual symmetric quotient graph. -/
theorem coefficients_eq_zero_of_graph (v : Fin 14 → K)
    (hv : ∀ A : Symmetric3 K,
      ∑ i : Fin 14, v i * (coordinateBasis14 K).equivFun (graph K A) i = 0) : v = 0 := by
  classical
  let φ : Coordinates K →ₗ[K] K :=
    ∑ i : Fin 14, v i • (coordinateBasis14 K).coord i
  have hφ : φ = 0 := by
    apply linearMap_eq_zero_of_graph K
    intro A
    have hvA := hv A
    rw [Basis.equivFun_apply] at hvA
    simpa only [φ, LinearMap.sum_apply, LinearMap.smul_apply,
      Basis.coord_apply, smul_eq_mul] using hvA
  funext j
  have h := LinearMap.congr_fun hφ (coordinateBasis14 K j)
  simpa [φ, Basis.coord_apply, Finsupp.single_apply] using h

end CharacteristicZero

end M9Native.LagrangianGraphSpan
end

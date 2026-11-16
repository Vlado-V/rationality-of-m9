module

public import M9StacksIntegration.MukaiConormalPrimitive
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual primitive first-jet annihilator at the standard quotient

All vectors and forms live in the actual primitive third exterior power
and its actual dual. The constant vector and the six linear `p` vectors
are the literal first-jet coordinates of the standard LG quotient. Their
annihilator is canonically the seven-dimensional `b+q` coordinate space.
This is a linear first-jet calculation, not yet an identification with
the native ideal-sheaf conormal at a scheme point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

namespace M9Native.MukaiConormalOrigin

open LagrangianField MukaiConormalPrimitive

variable (K : Type*) [Field K] [CharZero K]

def symmetricUnit (i j : Fin 3) : Symmetric3 K :=
  ⟨(Matrix.single i j (1 : K) + Matrix.single j i (1 : K) : Matrix (Fin 3) (Fin 3) K), by
    change (Matrix.single i j (1 : K) + Matrix.single j i (1 : K)).transpose =
      Matrix.single i j 1 + Matrix.single j i 1
    rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single]
    exact add_comm _ _⟩

omit [CharZero K] in
theorem trace_symmetricUnit (S : Symmetric3 K) (i j : Fin 3) :
    (∑ a : Fin 3, ∑ b : Fin 3, S.val a b * (symmetricUnit K i j).val a b) =
      S.val i j + S.val j i := by
  fin_cases i <;> fin_cases j <;>
    simp [symmetricUnit, Fin.sum_univ_succ, Matrix.single_apply] <;> ring

theorem symmetric_eq_zero_of_trace_zero (S : Symmetric3 K)
    (h : ∀ T : Symmetric3 K, (∑ i : Fin 3, ∑ j : Fin 3, S.val i j * T.val i j) = 0) :
    S = 0 := by
  apply Subtype.ext
  ext i j
  have hz := h (symmetricUnit K i j)
  rw [trace_symmetricUnit] at hz
  have he : S.val j i = S.val i j := congrFun (congrFun S.property i) j
  rw [he, ← two_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem conormalForm_injective : Function.Injective (conormalForm K) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : conormalForm K v = 0 := hv
  have hc : v.1 = 0 := by
    have h := congrArg (fun ell : Module.Dual K (Primitive K) =>
      ell (primitiveEquiv K (0,0,0,1))) hz
    simpa [conormalForm_coordinates] using h
  have hs : v.2 = 0 := by
    apply symmetric_eq_zero_of_trace_zero
    intro T
    have h := congrArg (fun ell : Module.Dual K (Primitive K) =>
      ell (primitiveEquiv K (0,T,0,0))) hz
    simpa [conormalForm_coordinates] using h
  exact Prod.ext hc hs

def originPoint : Primitive K := primitiveEquiv K (1,0,0,0)

def jetCoordinates : Symmetric3 K →ₗ[K] Coordinates K :=
  (0 : Symmetric3 K →ₗ[K] K).prod
    ((0 : Symmetric3 K →ₗ[K] Symmetric3 K).prod
      ((LinearMap.id : Symmetric3 K →ₗ[K] Symmetric3 K).prod
        (0 : Symmetric3 K →ₗ[K] K)))

def originJet : Symmetric3 K →ₗ[K] Primitive K :=
  (primitiveEquiv K).toLinearMap.comp (jetCoordinates K)

theorem originJet_apply (A : Symmetric3 K) :
    originJet K A = primitiveEquiv K (0,0,A,0) := rfl

/-- Value and all six first-jet evaluations on ACTUAL primitive forms. -/
def firstJetMap : Module.Dual K (Primitive K) →ₗ[K]
    K × Module.Dual K (Symmetric3 K) where
  toFun ell := (ell (originPoint K), ell.comp (originJet K))
  map_add' _a _b := rfl
  map_smul' _c _a := rfl

def originConormal : Submodule K (Module.Dual K (Primitive K)) :=
  LinearMap.ker (firstJetMap K)

theorem firstJetMap_surjective : Function.Surjective (firstJetMap K) := by
  rintro ⟨c, l⟩
  let q : Coordinates K →ₗ[K] K :=
    { toFun := fun r => c * r.1 + l r.2.2.1
      map_add' := by intro r s; simp [mul_add]; ring
      map_smul' := by intro a r; simp; ring }
  refine ⟨q.comp (primitiveEquiv K).symm.toLinearMap, ?_⟩
  apply Prod.ext
  · simp [firstJetMap, originPoint, q]
  · ext A
    simp [firstJetMap, originJet_apply, q]

theorem finrank_originConormal : Module.finrank K (originConormal K) = 7 := by
  have h := (firstJetMap K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (firstJetMap_surjective K), finrank_top] at h
  have ht : Module.finrank K (K × Module.Dual K (Symmetric3 K)) = 7 := by
    simp [Module.finrank_prod]
  have hs : Module.finrank K (Module.Dual K (Primitive K)) = 14 := by
    exact (Module.finrank_eq_card_basis ((LagrangianPluckerLinear.primitiveBasis14 K).dualBasis)).trans
      (Fintype.card_fin 14)
  change _ + Module.finrank K (originConormal K) = _ at h
  omega

theorem conormalForm_mem_originConormal (v : MukaiConormalPencil.ConormalCoordinates K) :
    conormalForm K v ∈ originConormal K := by
  change firstJetMap K (conormalForm K v) = 0
  apply Prod.ext
  · simp [firstJetMap, originPoint, conormalForm_coordinates]
  · ext A
    simp [firstJetMap, originJet_apply, conormalForm_coordinates]

def originConormalMap : MukaiConormalPencil.ConormalCoordinates K →ₗ[K] originConormal K :=
  (conormalForm K).codRestrict (originConormal K) (conormalForm_mem_originConormal K)

set_option backward.isDefEq.respectTransparency true in
theorem originConormalMap_bijective : Function.Bijective (originConormalMap K) := by
  have hi : Function.Injective (originConormalMap K) := fun v w h =>
    conormalForm_injective K (congrArg Subtype.val h)
  have hd : Module.finrank K (MukaiConormalPencil.ConormalCoordinates K) =
      Module.finrank K (originConormal K) := by
    rw [finrank_originConormal]
    simp [MukaiConormalPencil.ConormalCoordinates, Module.finrank_prod]
  have hs : Function.Surjective (originConormalMap K) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq (K := K) (V := originConormal K)
      (S := (originConormalMap K).range)
    calc
      _ = Module.finrank K (MukaiConormalPencil.ConormalCoordinates K) :=
        LinearMap.finrank_range_of_inj hi
      _ = _ := hd
  exact ⟨hi, hs⟩

/-- The exact b-plus-q coordinate equivalence for the actual native
primitive-form first-jet annihilator. -/
def originConormalIso : MukaiConormalPencil.ConormalCoordinates K ≃ₗ[K] originConormal K :=
  LinearEquiv.ofBijective (originConormalMap K) (originConormalMap_bijective K)

theorem originConormalIso_apply (v : MukaiConormalPencil.ConormalCoordinates K) :
    (originConormalIso K v).val = conormalForm K v := rfl

end M9Native.MukaiConormalOrigin

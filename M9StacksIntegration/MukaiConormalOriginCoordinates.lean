module

public import M9StacksIntegration.MukaiConormalOrigin
public import M9StacksIntegration.LagrangianPluckerFirstJet

/-! The actual constant-coordinate pivot and primitive-form coordinates
for the first-jet annihilator.  The pivot retains the original finite
reindexing of the native primitive basis. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

universe u

namespace M9Native.MukaiConormalOriginCoordinates

open LagrangianField MukaiConormalOrigin

def coordinateIndexEquiv : CoordinateIndex ≃ Fin 14 :=
  Fintype.equivFinOfCardEq (by simp [CoordinateIndex])

def originPivot : Fin 14 := coordinateIndexEquiv (.inl ())

variable (K : Type u) [Field K] [CharZero K]

omit [CharZero K] in
theorem coordinateBasis14_originPivot :
    coordinateBasis14 K originPivot = (1,0,0,0) := by
  change (coordinateBasis K).reindex coordinateIndexEquiv
    (coordinateIndexEquiv (.inl ())) = _
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  simp [coordinateBasis]
  rfl

theorem primitiveBasis14_originPivot :
    LagrangianPluckerLinear.primitiveBasis14 K originPivot = originPoint K := by
  rw [LagrangianPluckerLinear.primitiveBasis14, Module.Basis.map_apply,
    coordinateBasis14_originPivot]
  rfl

def formsCoordinates : Module.Dual K (Primitive K) ≃ₗ[K] (Fin 14 → K) :=
  (LagrangianPluckerLinear.primitiveBasis14 K).dualBasis.equivFun

theorem formsCoordinates_apply (ell : Module.Dual K (Primitive K)) (j : Fin 14) :
    formsCoordinates K ell j = ell (LagrangianPluckerLinear.primitiveBasis14 K j) := by
  simp only [formsCoordinates, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]

theorem formsCoordinates_symm_basis (v : Fin 14 → K) (j : Fin 14) :
    (formsCoordinates K).symm v (LagrangianPluckerLinear.primitiveBasis14 K j) = v j := by
  rw [← formsCoordinates_apply, LinearEquiv.apply_symm_apply]

/-- This is the actual homogeneous coordinate whose basis vector is the
constant Plucker vector; its numeric label is not chosen independently. -/
theorem formsCoordinates_symm_origin (v : Fin 14 → K) :
    (formsCoordinates K).symm v (originPoint K) = v originPivot := by
  rw [← primitiveBasis14_originPivot]
  exact formsCoordinates_symm_basis K v originPivot

theorem formsCoordinates_symm_apply (v : Fin 14 → K) (w : Primitive K) :
    (formsCoordinates K).symm v w =
      ∑ j : Fin 14, v j * (LagrangianPluckerLinear.primitiveBasis14 K).equivFun w j := by
  let b := LagrangianPluckerLinear.primitiveBasis14 K
  calc
    _ = (formsCoordinates K).symm v
        (∑ j : Fin 14, b.equivFun w j • b j) := congrArg _ (b.sum_repr w).symm
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      have hb : (formsCoordinates K).symm v (b j) = v j := formsCoordinates_symm_basis K v j
      rw [hb]
      exact mul_comm (b.equivFun w j) (v j)

theorem formsCoordinates_symm_originJet (v : Fin 14 → K) (B : Symmetric3 K) :
    (formsCoordinates K).symm v (originJet K B) =
      ∑ j : Fin 14, v j * (LagrangianPluckerLinear.primitiveBasis14 K).equivFun
        (primitiveEquiv K (0,0,B,0)) j :=
  formsCoordinates_symm_apply K v _

/-- A common nonzero change of line trivialization preserves the literal
first-jet annihilator. -/
theorem smul_mem_originConormal_iff (a : K) (ha : a ≠ 0)
    (ell : Module.Dual K (Primitive K)) :
    a • ell ∈ originConormal K ↔ ell ∈ originConormal K := by
  change firstJetMap K (a • ell) = 0 ↔ firstJetMap K ell = 0
  rw [map_smul, smul_eq_zero_iff_right ha]

omit [CharZero K] in
/-- Two actual line coordinates differ by a constructed common nonzero
scalar, with no multiplier supplied as data. -/
theorem exists_common_scalar {L : Type u} [AddCommGroup L] [Module K L]
    (e f : L ≃ₗ[K] K) :
    ∃ a : K, a ≠ 0 ∧ ∀ v : L, e v = a * f v := by
  let a := e (f.symm 1)
  have ha : a ≠ 0 := by
    intro h
    have hz : f.symm (1 : K) = 0 := e.injective (h.trans (map_zero e).symm)
    have h1 := congrArg f hz
    rw [LinearEquiv.apply_symm_apply, map_zero] at h1
    exact one_ne_zero h1
  refine ⟨a, ha, ?_⟩
  intro v
  have hv : v = f v • f.symm (1 : K) := by
    apply f.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    e v = e (f v • f.symm (1 : K)) := congrArg e hv
    _ = f v * a := e.map_smul _ _
    _ = a * f v := mul_comm _ _

end M9Native.MukaiConormalOriginCoordinates

module

public import StacksFrontier.LinearAlgebra.TensorProduct.SubmoduleBaseChange
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual ranks of field-linear maps survive genuine scalar extension.
The image is the actual base-changed submodule, identified by the native
flat tensor embedding; no rank equality is supplied as data. -/

@[expose] public noncomputable section
set_option autoImplicit false

open Module
open scoped TensorProduct

namespace M9Native.FieldBaseChangeRank

universe u v w w'

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N]
    [Module K M] [Module K N]

theorem finrank_range_baseChange (f : M →ₗ[K] N) :
    finrank L (LinearMap.range (f.baseChange L)) = finrank K (LinearMap.range f) := by
  rw [ArtinReesBaseChange.range_baseChange]
  exact (Submodule.toBaseChange.toLinearEquiv L (LinearMap.range f)).finrank_eq.symm.trans
    Module.finrank_baseChange

section Equiv

variable {V : Type*} {W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]

theorem finrank_range_equiv (f : M →ₗ[K] N) (e : V ≃ₗ[K] M) (e' : N ≃ₗ[K] W) :
    finrank K (LinearMap.range (e'.toLinearMap.comp (f.comp e.toLinearMap))) =
      finrank K (LinearMap.range f) := by
  rw [LinearMap.range_comp, LinearEquiv.finrank_map_eq, LinearEquiv.range_comp]

end Equiv

section Restriction

variable {V : Type*} {W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module L V] [Module L W] [Module K V] [Module K W]
    [IsScalarTower K L V] [IsScalarTower K L W]

theorem finrank_range_restrictScalars (f : V →ₗ[L] W) (h : finrank K L = 1) :
    finrank K (LinearMap.range (f.restrictScalars K)) = finrank L (LinearMap.range f) := by
  rw [LinearMap.range_restrictScalars]
  have ht := Module.finrank_mul_finrank K L (LinearMap.range f)
  have he : (LinearMap.range f).restrictScalars K ≃ₗ[K] LinearMap.range f :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact he.finrank_eq.trans (by simpa only [h, one_mul] using ht.symm)

end Restriction

section Tower

variable {R : Type*} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]

theorem finrank_range_baseChange_tower (f : P →ₗ[R] Q) :
    finrank L (LinearMap.range (f.baseChange L)) =
      finrank K (LinearMap.range (f.baseChange K)) := by
  have h := finrank_range_baseChange K L (f.baseChange K)
  rw [LinearMap.baseChange_baseChange] at h
  rw [finrank_range_equiv] at h
  exact h

end Tower

end M9Native.FieldBaseChangeRank

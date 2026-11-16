module

public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Tactic.FinCases

/-!
# The canonical exterior-square formula for a tensor line

The displayed isomorphism is computed using a trivialization of the actual
rank-one module. Its formula on decomposable wedges proves independence of
that trivialization. This is the module calculation used to verify the
canonical sheaf map stalkwise; no determinant identity is assumed.

The imported exterior-power comparison is the proved native helper in
Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace M9Native.ExteriorTensorLine

variable {R : Type u} [CommRing R]
  {V : Type v} [AddCommGroup V] [Module R V]
  {L : Type w} [AddCommGroup L] [Module R L]

/-- The actual decomposable two-vector in the exterior algebra. -/
def wedge (v w : V) : ⋀[R]^2 V :=
  exteriorPower.ιMulti R 2 ![v, w]

private theorem update_pair_zero {T : Type*} (v w x : T) :
    Function.update (![v, w] : Fin 2 → T) 0 x = ![x, w] := by
  ext i
  fin_cases i <;> simp

private theorem update_pair_one {T : Type*} (v w x : T) :
    Function.update (![v, w] : Fin 2 → T) 1 x = ![v, x] := by
  ext i
  fin_cases i <;> simp

theorem wedge_smul_left (a : R) (v w : V) :
    wedge (R := R) (a • v) w = a • wedge (R := R) v w := by
  simpa only [update_pair_zero, wedge] using
    (exteriorPower.ιMulti R 2 (M := V)).map_update_smul ![v, w] 0 a v

theorem wedge_smul_right (a : R) (v w : V) :
    wedge (R := R) v (a • w) = a • wedge (R := R) v w := by
  simpa only [update_pair_one, wedge] using
    (exteriorPower.ιMulti R 2 (M := V)).map_update_smul ![v, w] 1 a w

theorem wedge_self (v : V) : wedge (R := R) v v = 0 := by
  exact (exteriorPower.ιMulti R 2 (M := V)).map_eq_zero_of_eq ![v, v]
    (by simp : (![v, v] : Fin 2 → V) 0 = (![v, v] : Fin 2 → V) 1)
    (by decide : (0 : Fin 2) ≠ 1)

theorem wedge_add_left (v w x : V) :
    wedge (R := R) (v + w) x = wedge (R := R) v x + wedge (R := R) w x := by
  simpa only [update_pair_zero, wedge] using
    (exteriorPower.ιMulti R 2 (M := V)).map_update_add ![v, x] 0 v w

theorem wedge_add_right (v w x : V) :
    wedge (R := R) v (w + x) = wedge (R := R) v w + wedge (R := R) v x := by
  simpa only [update_pair_one, wedge] using
    (exteriorPower.ιMulti R 2 (M := V)).map_update_add ![v, w] 1 w x

/-- The actual universal bilinear wedge. -/
def wedgeBilinear : V →ₗ[R] V →ₗ[R] ⋀[R]^2 V where
  toFun v :=
    { toFun := wedge v
      map_add' := wedge_add_right v
      map_smul' := fun a w => wedge_smul_right a v w }
  map_add' v w := LinearMap.ext fun x => wedge_add_left v w x
  map_smul' a v := LinearMap.ext fun w => wedge_smul_left a v w

/-- The canonical quotient from the tensor square to the exterior square. -/
def wedgeQuotient : V ⊗[R] V →ₗ[R] ⋀[R]^2 V :=
  TensorProduct.lift wedgeBilinear

@[simp] theorem wedgeQuotient_tmul (v w : V) :
    wedgeQuotient (v ⊗ₜ[R] w) = wedge (R := R) v w := rfl

theorem wedge_ext {N : Type*} [AddCommGroup N] [Module R N]
    {f g : (⋀[R]^2 V) →ₗ[R] N}
    (h : ∀ v w, f (wedge (R := R) v w) = g (wedge (R := R) v w)) : f = g := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : (![v 0, v 1] : Fin 2 → V) = v := by
    ext i
    fin_cases i <;> rfl
  simpa only [wedge, hv, LinearMap.compAlternatingMap_apply] using h (v 0) (v 1)

theorem wedgeQuotient_surjective : Function.Surjective (wedgeQuotient (R := R) (V := V)) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← exteriorPower.ιMulti_span R 2 V, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine ⟨v 0 ⊗ₜ[R] v 1, ?_⟩
  have hv : (![v 0, v 1] : Fin 2 → V) = v := by
    ext i
    fin_cases i <;> rfl
  exact congrArg (exteriorPower.ιMulti R 2) hv

theorem exterior_map_wedge {N : Type*} [AddCommGroup N] [Module R N]
    (f : V →ₗ[R] N) (v w : V) :
    exteriorPower.map 2 f (wedge v w) = wedge (f v) (f w) := by
  rw [wedge, exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem exterior_map_comp_wedgeQuotient {N : Type*} [AddCommGroup N] [Module R N]
    (f : V →ₗ[R] N) :
    exteriorPower.map 2 f ∘ₗ wedgeQuotient =
      wedgeQuotient ∘ₗ TensorProduct.map f f :=
  TensorProduct.ext' fun v w => exterior_map_wedge f v w

/-- Tensoring with a genuinely trivialized line, using the actual tensor
unitor rather than an arbitrary equivalence of the resulting modules. -/
def lineNormalization (b : L ≃ₗ[R] R) : V ⊗[R] L ≃ₗ[R] V :=
  TensorProduct.congr (LinearEquiv.refl R V) b ≪≫ₗ TensorProduct.rid R V

@[simp] theorem lineNormalization_tmul (b : L ≃ₗ[R] R) (v : V) (l : L) :
    lineNormalization (V := V) b (v ⊗ₜ[R] l) = b l • v := by
  simp [lineNormalization]

@[simp] theorem lineNormalization_symm_apply (b : L ≃ₗ[R] R) (v : V) :
    (lineNormalization (V := V) b).symm v = v ⊗ₜ[R] b.symm 1 := by
  apply (lineNormalization (V := V) b).injective
  simp

/-- Every tensor with a rank-one module is pure, by its actual line basis. -/
theorem tensor_eq_pure (b : L ≃ₗ[R] R) (z : V ⊗[R] L) :
    ∃ v : V, z = v ⊗ₜ[R] b.symm 1 := by
  exact ⟨lineNormalization (V := V) b z,
    ((lineNormalization (V := V) b).symm_apply_apply z).symm.trans
      (lineNormalization_symm_apply b _)⟩

/-- The normalization of the target exterior square and two line factors. -/
def targetNormalization (b : L ≃ₗ[R] R) :
    (⋀[R]^2 V) ⊗[R] (L ⊗[R] L) ≃ₗ[R] ⋀[R]^2 V :=
  TensorProduct.congr (LinearEquiv.refl R _) 
      (TensorProduct.congr b b ≪≫ₗ TensorProduct.lid R R) ≪≫ₗ
    TensorProduct.rid R _

@[simp] theorem targetNormalization_tmul (b : L ≃ₗ[R] R)
    (z : ⋀[R]^2 V) (l m : L) :
    targetNormalization (V := V) b (z ⊗ₜ[R] (l ⊗ₜ[R] m)) =
      (b l * b m) • z := by
  simp [targetNormalization]

/-- The actual exterior-power functor and tensor unitors supply this
isomorphism. The next formula identifies it canonically. -/
def moduleIso (b : L ≃ₗ[R] R) :
    (⋀[R]^2 (V ⊗[R] L)) ≃ₗ[R] (⋀[R]^2 V) ⊗[R] (L ⊗[R] L) :=
  exteriorPowerCongr 2 (lineNormalization (V := V) b) ≪≫ₗ
    (targetNormalization (V := V) b).symm

/-- The canonical formula, including the precise order of the two line
factors. -/
theorem moduleIso_wedge_tmul (b : L ≃ₗ[R] R) (v w : V) (l m : L) :
    moduleIso (V := V) b (wedge (v ⊗ₜ[R] l) (w ⊗ₜ[R] m)) =
      wedge v w ⊗ₜ[R] (l ⊗ₜ[R] m) := by
  apply (targetNormalization (V := V) b).injective
  simp only [moduleIso, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    targetNormalization_tmul]
  change exteriorPower.map 2 (lineNormalization (V := V) b).toLinearMap
      (exteriorPower.ιMulti R 2 ![v ⊗ₜ[R] l, w ⊗ₜ[R] m]) = _
  rw [exteriorPower.map_apply_ιMulti]
  change wedge (b l • v) (b m • w) = _
  rw [wedge_smul_left, wedge_smul_right, smul_smul]

/-- The decomposable formula makes the isomorphism independent of the
trivialization used to check it. -/
theorem moduleIso_independent (b c : L ≃ₗ[R] R) :
    (moduleIso (V := V) b).toLinearMap = (moduleIso (V := V) c).toLinearMap := by
  refine wedge_ext (R := R) (V := V ⊗[R] L)
    (N := (⋀[R]^2 V) ⊗[R] (L ⊗[R] L))
    (f := (moduleIso (V := V) b).toLinearMap)
    (g := (moduleIso (V := V) c).toLinearMap) ?_
  intro z z'
  obtain ⟨v, rfl⟩ := tensor_eq_pure b z
  obtain ⟨w, rfl⟩ := tensor_eq_pure b z'
  exact (moduleIso_wedge_tmul b v w _ _).trans
    (moduleIso_wedge_tmul c v w _ _).symm

/-- Before exterior descent, the canonical map is the middle-four
interchange followed by the actual wedge and identity. -/
def quadraticMap :
    (V ⊗[R] L) ⊗[R] (V ⊗[R] L) →ₗ[R] (⋀[R]^2 V) ⊗[R] (L ⊗[R] L) :=
  TensorProduct.map wedgeQuotient LinearMap.id ∘ₗ
    (TensorProduct.tensorTensorTensorComm R V L V L).toLinearMap

@[simp] theorem quadraticMap_tmul (v w : V) (l m : L) :
    quadraticMap ((v ⊗ₜ[R] l) ⊗ₜ[R] (w ⊗ₜ[R] m)) =
      wedge v w ⊗ₜ[R] (l ⊗ₜ[R] m) := by
  simp [quadraticMap]

theorem moduleIso_comp_wedgeQuotient (b : L ≃ₗ[R] R) :
    (moduleIso (V := V) b).toLinearMap ∘ₗ wedgeQuotient = quadraticMap := by
  apply TensorProduct.ext'
  intro z z'
  obtain ⟨v, rfl⟩ := tensor_eq_pure b z
  obtain ⟨w, rfl⟩ := tensor_eq_pure b z'
  exact (moduleIso_wedge_tmul b v w _ _).trans (quadraticMap_tmul v w _ _).symm

theorem quadraticMap_diagonal (b : L ≃ₗ[R] R) (z : V ⊗[R] L) :
    quadraticMap (z ⊗ₜ[R] z) = 0 := by
  rw [← moduleIso_comp_wedgeQuotient b]
  simp [wedge_self]

/-- Naturality for the actual linear maps of both the vector module and
the line. This also identifies the isomorphism with the universal wedge
pairing used in tensor and determinant constructions. -/
theorem moduleIso_naturality
    {V' L' : Type*} [AddCommGroup V'] [Module R V'] [AddCommGroup L'] [Module R L']
    (b : L ≃ₗ[R] R) (c : L' ≃ₗ[R] R) (f : V →ₗ[R] V') (g : L →ₗ[R] L') :
    TensorProduct.map (exteriorPower.map 2 f) (TensorProduct.map g g) ∘ₗ
        (moduleIso (V := V) b).toLinearMap =
      (moduleIso (V := V') c).toLinearMap ∘ₗ
        exteriorPower.map 2 (TensorProduct.map f g) := by
  refine wedge_ext (R := R) (V := V ⊗[R] L)
    (N := (⋀[R]^2 V') ⊗[R] (L' ⊗[R] L')) ?_
  intro z z'
  obtain ⟨v, rfl⟩ := tensor_eq_pure b z
  obtain ⟨w, rfl⟩ := tensor_eq_pure b z'
  simp only [LinearMap.comp_apply, moduleIso_wedge_tmul, TensorProduct.map_tmul,
    exterior_map_wedge, LinearEquiv.coe_coe]

end M9Native.ExteriorTensorLine

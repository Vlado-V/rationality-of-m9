module

public import M9.RadicalMapProjective

/-! # Exact transport of actual radical fibers by form isometries -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.RadicalMap

open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isometry_symm (B : LinearMap.BilinForm K V) (g : V ≃ₗ[K] V)
    (hg : ∀ x y, B (g x) (g y) = B x y) :
    ∀ x y, B (g.symm x) (g.symm y) = B x y := by
  intro x y
  have h := hg (g.symm x) (g.symm y)
  simpa only [g.apply_symm_apply] using h.symm

/-- An actual isometry gives an actual equivalence of subspace fibers. -/
def subspaceFiberIsometryEquiv (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, B (g x) (g y) = B x y) (L : Submodule K V) :
    {U : Submodule K V // finrank K U = 9 ∧ RadicalFiber.radical B U = L} ≃
      {U : Submodule K V // finrank K U = 9 ∧
        RadicalFiber.radical B U = L.map g.toLinearMap} where
  toFun U := ⟨U.val.map g.toLinearMap,by rw [g.finrank_map_eq]; exact U.property.1,by
    rw [← radical_map_isometry B hB g hg,U.property.2]⟩
  invFun U := ⟨U.val.map g.symm.toLinearMap,by rw [g.symm.finrank_map_eq]; exact U.property.1,by
    rw [← radical_map_isometry B hB g.symm (isometry_symm B g hg),U.property.2,
      ← Submodule.map_comp,g.symm_comp,Submodule.map_id]⟩
  left_inv U := by
    apply Subtype.ext
    change (U.val.map g.toLinearMap).map g.symm.toLinearMap = U.val
    rw [← Submodule.map_comp,g.symm_comp,Submodule.map_id]
  right_inv U := by
    apply Subtype.ext
    change (U.val.map g.symm.toLinearMap).map g.toLinearMap = U.val
    rw [← Submodule.map_comp,g.comp_symm,Submodule.map_id]

/-- The fiber of the genuine projective radical map transports by the genuine isometry. -/
def pointFiberIsometryEquiv (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, B (g x) (g y) = B x y) (L : Projectivization K V) :
    {U : RankEightPlane B // radicalPoint B U = L} ≃
      {U : RankEightPlane B // radicalPoint B U =
        Projectivization.map g.toLinearMap g.injective L} := by
  refine (pointFiberEquiv B L).trans ((subspaceFiberIsometryEquiv B hB g hg L.submodule).trans ?_)
  rw [← projective_submodule_map g L]
  exact (pointFiberEquiv B (Projectivization.map g.toLinearMap g.injective L)).symm

end M9.RadicalMap

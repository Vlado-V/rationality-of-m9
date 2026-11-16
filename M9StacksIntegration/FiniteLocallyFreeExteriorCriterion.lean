module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalkNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso

/-!
# Detecting isomorphisms by the actual top exterior power

A map between finite locally free sheaves of the same rank is an isomorphism
if its native top exterior map is an isomorphism.  The proof uses the genuine
stalk bases, naturality of the native exterior-power stalk comparison, and the
determinant of the original linear map.  Rank zero is included.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Sheaf

universe u v w

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.FiniteLocallyFreeExteriorCriterion

section Linear

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {r : ℕ}

/-- Surjectivity on the actual top exterior power makes the original matrix
determinant a unit over any commutative ring. -/
theorem isUnit_det_of_surjective_topExterior
    (b : Module.Basis (Fin r) R M) (c : Module.Basis (Fin r) R N)
    (α : M →ₗ[R] N) (h : Function.Surjective (exteriorPower.map r α)) :
    IsUnit (LinearMap.toMatrix b c α).det := by
  have hr : Submodule.map (Stacks.ExteriorPower.topEquiv c).toLinearMap
      (Ideal.span {(LinearMap.toMatrix b c α).det}) = ⊤ := by
    rw [← Stacks.ExteriorPower.range_map_eq_map_span b c α]
    exact LinearMap.range_eq_top.mpr h
  have hi : (Ideal.span {(LinearMap.toMatrix b c α).det} : Submodule R R) = ⊤ := by
    apply Submodule.map_injective_of_injective (Stacks.ExteriorPower.topEquiv c).injective
    rw [hr, Submodule.map_top, LinearMap.range_eq_top.mpr
      (Stacks.ExteriorPower.topEquiv c).surjective]
  exact Ideal.span_singleton_eq_top.mp hi

/-- A map of free modules of equal finite rank is bijective when its actual
top exterior map is surjective. -/
theorem bijective_of_surjective_topExterior
    (b : Module.Basis (Fin r) R M) (c : Module.Basis (Fin r) R N)
    (α : M →ₗ[R] N) (h : Function.Surjective (exteriorPower.map r α)) :
    Function.Bijective α := by
  classical
  let A := LinearMap.toMatrix b c α
  have hA : IsUnit A.det := isUnit_det_of_surjective_topExterior b c α h
  let β := Matrix.toLin c b A⁻¹
  have hβα : β.comp α = LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b c b β α, LinearMap.toMatrix_toLin, LinearMap.toMatrix_id]
    exact Matrix.nonsing_inv_mul A hA
  have hαβ : α.comp β = LinearMap.id := by
    apply (LinearMap.toMatrix c c).injective
    rw [LinearMap.toMatrix_comp c b c α β, LinearMap.toMatrix_toLin, LinearMap.toMatrix_id]
    exact Matrix.mul_nonsing_inv A hA
  have hl : Function.LeftInverse β α := fun x => LinearMap.congr_fun hβα x
  have hr : Function.RightInverse β α := fun x => LinearMap.congr_fun hαβ x
  exact ⟨hl.injective, hr.surjective⟩

end Linear

section Sheaves

variable {X : Scheme.{u}} {E F : X.Modules}

/-- The genuine exterior-power stalk comparison transfers surjectivity of
the native exterior map to the exterior power of the original stalk map. -/
theorem surjective_topExterior_stalkMap (α : E ⟶ F) (r : ℕ)
    [IsIso (Scheme.Modules.exteriorPowerMap α (r : ℤ))] (x : X) :
    Function.Surjective (exteriorPower.map r (PresheafOfModules.stalkMapL x α.val)) := by
  let A := _root_.SheafOfModules.algebras (Opens.grothendieckTopology X) E
  let B := _root_.SheafOfModules.algebras (Opens.grothendieckTopology X) F
  let eA := _root_.SheafOfModules.exteriorPowerStalkEquiv
    A.exterior A.exteriorGenerator A.exterior_isExteriorAlgebra r x
  let eB := _root_.SheafOfModules.exteriorPowerStalkEquiv
    B.exterior B.exteriorGenerator B.exterior_isExteriorAlgebra r x
  have htop := (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (Scheme.Modules.exteriorPowerMap α (r : ℤ))).1 inferInstance x
  intro z
  obtain ⟨q, hq⟩ := htop.2 (eB.symm z)
  refine ⟨eA q, ?_⟩
  have hn : eB (PresheafOfModules.stalkMapL x
      (Scheme.Modules.exteriorPowerMap α (r : ℤ)).val q) =
      exteriorPower.map r (PresheafOfModules.stalkMapL x α.val) (eA q) :=
    _root_.SheafOfModules.exteriorPowerStalkEquiv_naturality
      A.exterior_isExteriorAlgebra B.exterior_isExteriorAlgebra α r x q
  exact hn.symm.trans ((congrArg eB hq).trans (eB.apply_symm_apply z))

/-- Invertibility of the actual top exterior map makes every original
stalk map bijective. -/
theorem bijective_stalkMap_of_isIso_topExterior (α : E ⟶ F) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [IsIso (Scheme.Modules.exteriorPowerMap α (r : ℤ))] (x : X) :
    Function.Bijective (PresheafOfModules.stalkMapL x α.val) := by
  exact bijective_of_surjective_topExterior
    (Stacks.SheafOfModules.TopWedge.stalkBasis E r x)
    (Stacks.SheafOfModules.TopWedge.stalkBasis F r x)
    (PresheafOfModules.stalkMapL x α.val) (surjective_topExterior_stalkMap α r x)

/-- The actual native top exterior power detects isomorphisms of finite
locally free sheaves of equal rank, on an arbitrary scheme. -/
theorem isIso_of_isIso_exteriorPowerMap (α : E ⟶ F) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [IsIso (Scheme.Modules.exteriorPowerMap α (r : ℤ))] : IsIso α := by
  apply (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap α).2
  intro x
  exact bijective_stalkMap_of_isIso_topExterior α r x

end Sheaves

end M9Native.FiniteLocallyFreeExteriorCriterion

module

public import M9StacksIntegration.MukaiCubicFreeSheaf

/-! Actual free-coordinate pullback formulas. All coefficients are pulled
by the original map on global functions; the constant fourteen-coordinate
sections retain their literal ground-field coefficients. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators

universe u

namespace M9Native.MukaiFreePullbackCoordinates

open LagrangianMatrixChart LagrangianFreeMatrixPullback AlgebraicGeometry.Grassmannian
open MukaiConstantFreeBasis MukaiCubicFreeSheaf

variable {X Y : Scheme.{u}}

theorem freeCoordinates_pullback (p : Y ⟶ X) (r : ℕ)
    (s : Γ(freeOn X r, ⊤)) (i : Fin r) :
    freeSectionCoordinates Y r
      ((pullbackFreeIso p r).hom.app ⊤ (pullbackGlobalSections p (freeOn X r) s)) i =
      p.appTop (freeSectionCoordinates X r s i) := by
  classical
  conv_lhs => rw [eq_sum_coordinates_basis X r s]
  simp only [map_sum, SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, FiniteFreeBasisPullback.freeBasisSection_pullback,
    map_smul, Finset.sum_apply, Pi.smul_apply, freeCoordinates_basis, smul_eq_mul]
  simp

theorem baseScalar_comp (R : CommRingCat.{u}) (f : X ⟶ Spec R) (p : Y ⟶ X) (a : R) :
    baseScalar R (p ≫ f) a = p.appTop (baseScalar R f a) := by
  simp only [baseScalar, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem formSection_pullback (K : Type u) [Field K] [CharZero K]
    (f : X ⟶ Spec (.of K)) (p : Y ⟶ X) (ell : MukaiPrimitiveQuartic.Forms K) :
    (pullbackFreeIso p 14).hom.app ⊤
      (pullbackGlobalSections p (freeOn X 14) (formSection K f ell)) =
      formSection K (p ≫ f) ell := by
  apply (freeSectionCoordinates Y 14).injective
  funext i
  rw [freeCoordinates_pullback]
  simp only [formSection_coordinates]
  exact (baseScalar_comp (.of K) f p _).symm

theorem dualFormSection_pullback (K : Type u) [Field K] [CharZero K]
    (f : X ⟶ Spec (.of K)) (p : Y ⟶ X)
    (ell : Module.Dual K (MukaiPrimitiveQuartic.Forms K)) :
    (pullbackFreeIso p 14).hom.app ⊤
      (pullbackGlobalSections p (freeOn X 14) (dualFormSection K f ell)) =
      dualFormSection K (p ≫ f) ell := by
  apply (freeSectionCoordinates Y 14).injective
  funext i
  rw [freeCoordinates_pullback]
  simp only [dualFormSection_coordinates]
  exact (baseScalar_comp (.of K) f p _).symm

theorem baseScalar_id (K : Type u) [Field K] (a : K) :
    baseScalar (.of K) (𝟙 (Spec (.of K))) a = (Scheme.ΓSpecIso (.of K)).inv.hom a := by
  simp only [baseScalar, Scheme.Hom.id_appTop, Category.comp_id]

/-- Every actual free-fourteen section over the ground-field point has
one and only one literal primitive coefficient vector. -/
theorem formSection_surjective (K : Type u) [Field K] [CharZero K] :
    Function.Surjective (formSection K (𝟙 (Spec (.of K)))) := by
  intro s
  let c : Fin 14 → K := fun i => (Scheme.ΓSpecIso (.of K)).hom
    (freeSectionCoordinates (Spec (.of K)) 14 s i)
  let ell : MukaiPrimitiveQuartic.Forms K := (formsBasis K).equivFun.symm c
  refine ⟨ell, ?_⟩
  apply (freeSectionCoordinates (Spec (.of K)) 14).injective
  funext i
  rw [formSection_coordinates, baseScalar_id]
  have hc : ell (LagrangianPluckerLinear.primitiveBasis14 K i) = c i := by
    have h := LinearEquiv.apply_symm_apply (formsBasis K).equivFun c
    simpa only [ell, formsBasis, Basis.equivFun_apply, Basis.dualBasis_repr] using congrFun h i
  rw [hc]
  exact congrArg (fun a => a.hom (freeSectionCoordinates (Spec (.of K)) 14 s i))
    (Scheme.ΓSpecIso (.of K)).hom_inv_id

end M9Native.MukaiFreePullbackCoordinates

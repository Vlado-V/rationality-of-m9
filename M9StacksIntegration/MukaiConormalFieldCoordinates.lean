module

public import M9StacksIntegration.MukaiConormalEulerPullback
public import M9StacksIntegration.MukaiConormalOriginCoordinates
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! Actual field-point coordinates of the original determinant-twisted
conormal Euler inclusion, and its derived seven-dimensional image. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalFieldCoordinates

open LagrangianGrassmannian LagrangianMatrixChart MukaiConormalEulerTwist
open MukaiConormalEulerPullback MukaiConormalOriginCoordinates
open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K]

def scalarEquiv : K ≃+* Γ(Spec (.of K),⊤) :=
  (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv

/-- The actual free-sheaf section coordinates, with the original field
scalar map of the native affine section functor. -/
def freeCoordinates (r : ℕ) :
    moduleSpecΓFunctor.obj (freeOn (Spec (.of K)) r) ≃ₗ[K] (Fin r → K) where
  toFun s i := (scalarEquiv K).symm (freeSectionCoordinates (Spec (.of K)) r s i)
  invFun v := (freeSectionCoordinates (Spec (.of K)) r).symm
    (fun i => scalarEquiv K (v i))
  left_inv s := by
    apply (freeSectionCoordinates (Spec (.of K)) r).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    exact (scalarEquiv K).apply_symm_apply _
  right_inv v := by
    funext i
    change (scalarEquiv K).symm ((freeSectionCoordinates (Spec (.of K)) r)
      ((freeSectionCoordinates (Spec (.of K)) r).symm (fun j => scalarEquiv K (v j))) i) = v i
    rw [LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
  map_add' s t := by
    funext i
    change (scalarEquiv K).symm (freeSectionCoordinates (Spec (.of K)) r
      ((show Γ(freeOn (Spec (.of K)) r,⊤) from s) +
        (show Γ(freeOn (Spec (.of K)) r,⊤) from t)) i) =
      (scalarEquiv K).symm (freeSectionCoordinates (Spec (.of K)) r s i) +
        (scalarEquiv K).symm (freeSectionCoordinates (Spec (.of K)) r t i)
    rw [map_add, Pi.add_apply, map_add]
  map_smul' a s := by
    funext i
    change (scalarEquiv K).symm
      (freeSectionCoordinates (Spec (.of K)) r
        (scalarEquiv K a • (show Γ(freeOn (Spec (.of K)) r,⊤) from s)) i) =
        a * (scalarEquiv K).symm (freeSectionCoordinates (Spec (.of K)) r s i)
    rw [map_smul]
    change (scalarEquiv K).symm
      (scalarEquiv K a * freeSectionCoordinates (Spec (.of K)) r s i) = _
    rw [map_mul, RingEquiv.symm_apply_apply]

theorem finite_and_finrank_sections (E : (Spec (.of K)).Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] :
    Module.Finite K (moduleSpecΓFunctor.obj E) ∧
      finrank K (moduleSpecΓFunctor.obj E) = r := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    (inferInstance : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r).isFiniteLocallyFree
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hfrom : IsIso E.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent E
  have hE := Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf E r
  have htilde := Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
    (@asIso _ _ _ _ E.fromTildeΓ hfrom).symm hE
  have hM := (tilde_isFiniteLocallyFreeOfRank_iff K (moduleSpecΓFunctor.obj E) r).mp htilde
  exact ⟨hM.finite, hM.finrank_eq⟩

variable [CharZero K] [IsAlgClosed K]

abbrev Source (p : Spec (.of K) ⟶ space K) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (MukaiConormalBundle.twistedConormal K))

/-- The original sheaf map is pulled back and read in the actual standard
free basis.  This is a constructed map, not an image specification. -/
def coefficientMap (p : Spec (.of K) ⟶ space K) : Source K p →ₗ[K] (Fin 14 → K) :=
  (freeCoordinates K 14).toLinearMap.comp
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (twistedConormalMap K) ≫
      (pullbackFreeIso p 14).hom)).hom

def formsMap (p : Spec (.of K) ⟶ space K) :
    Source K p →ₗ[K] Module.Dual K (LagrangianField.Primitive K) :=
  (formsCoordinates K).symm.toLinearMap.comp (coefficientMap K p)

theorem coefficientMap_injective (p : Spec (.of K) ⟶ space K) :
    Function.Injective (coefficientMap K p) := by
  let : Mono ((Scheme.Modules.pullback p).map (twistedConormalMap K)) :=
    pullback_twistedConormalMap_mono K p
  let : (moduleSpecΓFunctor (R := .of K)).IsRightAdjoint :=
    (tilde.adjunction (R := .of K)).isRightAdjoint
  have hi : Function.Injective
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (twistedConormalMap K) ≫
        (pullbackFreeIso p 14).hom)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact (freeCoordinates K 14).injective.comp hi

theorem formsMap_injective (p : Spec (.of K) ⟶ space K) :
    Function.Injective (formsMap K p) :=
  (formsCoordinates K).symm.injective.comp (coefficientMap_injective K p)

theorem source_finite_and_finrank (p : Spec (.of K) ⟶ space K) :
    Module.Finite K (Source K p) ∧ finrank K (Source K p) = 7 := by
  let := MukaiConormalRank.twistedConormal_rank K
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj (MukaiConormalBundle.twistedConormal K)) 7 :=
    isFiniteLocallyFreeOfRank_pullback p _ 7
  exact finite_and_finrank_sections K _ 7

theorem finrank_range_formsMap (p : Spec (.of K) ⟶ space K) :
    finrank K (LinearMap.range (formsMap K p)) = 7 :=
  (LinearMap.finrank_range_of_inj (formsMap_injective K p)).trans (source_finite_and_finrank K p).2

end M9Native.MukaiConormalFieldCoordinates

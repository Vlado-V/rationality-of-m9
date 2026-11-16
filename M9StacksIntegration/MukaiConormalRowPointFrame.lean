module

public import M9StacksIntegration.LagrangianFibreConormalMap
public import M9StacksIntegration.MukaiConormalChartFrame
public import M9StacksIntegration.MukaiConormalChartCovariance
public import M9StacksIntegration.LagrangianDualPullback
public import M9StacksIntegration.LagrangianFreeDualSections
public import M9StacksIntegration.TensorFreeRowProjection
public import M9StacksIntegration.FiniteLocallyFreeDualFaithful

/-!
# A genuine translated-frame normalization of the original five equation dual

The actual determinant frame supplies a nonzero unit functional in the
actual pulled determinant dual. The original five tensor projections
then give five actual source vectors. Their dual tensor inclusions read
off the coefficients, so the constructed map is injective. The proved
source rank five makes it bijective. No frame or matrix normalization is
supplied as an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.AlgebraicGeometry.ReflexiveModules
open scoped BigOperators

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

universe u
namespace M9Native.MukaiConormalRowPointFrame

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open MukaiConormalChartJets LagrangianTranslatedCharts LagrangianTranslatedDeterminantSections

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
  (i : X ⟶ space K) (p : Spec (.of K) ⟶ X)
  (g : Matrix.symplecticGroup (Fin 3) K) (z : Spec (.of K) ⟶ chart K)
  (hz : z ≫ translatedBigCell K g = p ≫ i)

abbrev PointLine :=
  (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback i).obj (determinantLine K))
abbrev PointDualLine := moduleSpecΓFunctor.obj
  ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback i).obj (dualSheaf (determinantLine K))))
abbrev PointSource := moduleSpecΓFunctor.obj
  ((Scheme.Modules.pullback p).obj (LagrangianFibreConormalMap.source K i))

/-- The literal translated frame is transported around the actual point square. -/
def pointLineFrame : PointLine K i p ≅ SheafOfModules.unit (Spec (.of K)).ringCatSheaf :=
  LineFramePullback.squareFrame p i z (translatedBigCell K g) hz.symm
    (determinantLine K) (translatedDeterminantIso K g)

/-- Both actual dual-pullback comparisons are the genuine native maps. -/
def pointDualLineIso :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback i).obj (dualSheaf (determinantLine K))) ≅
      dualSheaf (PointLine K i p) := by
  let hD := LagrangianFiveSectionModel.determinantLine_isInvertible K
  let hD1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (determinantLine K) 1 :=
    @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (space K) (determinantLine K) hD
  let hDi := isFiniteLocallyFreeOfRank_pullback i (determinantLine K) 1
  exact (Scheme.Modules.pullback p).mapIso
    (LagrangianDualPullback.dualPullbackIso i (determinantLine K) hD1.isFiniteLocallyFree) ≪≫
      LagrangianDualPullback.dualPullbackIso p
        ((Scheme.Modules.pullback i).obj (determinantLine K)) hDi.isFiniteLocallyFree

/-- The actual unit functional in the actual pulled original dual line. -/
def pointDualUnit : PointDualLine K i p :=
  (pointDualLineIso K i p).inv.app ⊤
    (LagrangianLocalIsotropy.functionalSection (PointLine K i p)
      (pointLineFrame K i p g z hz).hom)

omit [CharZero K] in
theorem pointDualUnit_ne_zero : pointDualUnit K i p g z hz ≠ 0 := by
  intro hzero
  let e := pointLineFrame K i p g z hz
  let m := e.inv.app ⊤ (1 : Γ(Spec (.of K), ⊤))
  have hτ : LagrangianLocalIsotropy.functionalSection (PointLine K i p) e.hom = 0 := by
    let d : PointDualLine K i p ≃ₗ[K] moduleSpecΓFunctor.obj (dualSheaf (PointLine K i p)) :=
      (moduleSpecΓFunctor.mapIso (pointDualLineIso K i p)).toLinearEquiv
    apply d.symm.injective
    change pointDualUnit K i p g z hz = d.symm 0
    exact hzero.trans d.symm.toLinearMap.map_zero.symm
  have heval : evalAt (PointLine K i p)
      (LagrangianLocalIsotropy.functionalSection (PointLine K i p) e.hom) m = 1 := by
    change e.hom.app ⊤ (e.inv.app ⊤ (1 : Γ(Spec (.of K), ⊤))) =
      (1 : Γ(Spec (.of K), ⊤))
    exact congrArg (fun a => a.app ⊤ (1 : Γ(Spec (.of K), ⊤))) e.inv_hom_id
  rw [hτ] at heval
  exact zero_ne_one heval

/-- The actual vector from the j-th original tensor projection. -/
def pointRowBasis (j : Fin 5) : PointSource K i p :=
  (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
    ((Scheme.Modules.pullback i).map (dualMap
      (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j)))))).hom
    (pointDualUnit K i p g z hz)

/-- The actual dual tensor inclusion reads a source coefficient. -/
def pointCoordinate (j : Fin 5) : PointSource K i p →ₗ[K] PointDualLine K i p :=
  (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
    ((Scheme.Modules.pullback i).map (dualMap
      (TensorFreeCoordinates.inclusion (space K) (determinantLine K) 5 (ULift.up j)))))).hom

omit [CharZero K] in
theorem pointCoordinate_pointRowBasis (j k : Fin 5) :
    pointCoordinate K i p j (pointRowBasis K i p g z hz k) =
      if j = k then pointDualUnit K i p g z hz else 0 := by
  classical
  have hδ : dualMap (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up k)) ≫
      dualMap (TensorFreeCoordinates.inclusion (space K) (determinantLine K) 5 (ULift.up j)) =
      if j = k then 𝟙 (dualSheaf (determinantLine K)) else 0 := by
    rw [← dualMap_comp, TensorFreeRowProjection.inclusion_comp_projection]
    by_cases h : j = k
    · simp only [h, ite_eq_left, dualMap_id]
    · simp only [ite_eq_right h, FiniteLocallyFreeDualFaithful.dualMap_zero]
  change (((Scheme.Modules.pullback p).map
      ((Scheme.Modules.pullback i).map (dualMap
        (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up k))))) ≫
    ((Scheme.Modules.pullback p).map
      ((Scheme.Modules.pullback i).map (dualMap
        (TensorFreeCoordinates.inclusion (space K) (determinantLine K) 5 (ULift.up j)))))).app ⊤
          (pointDualUnit K i p g z hz) = _
  rw [← Functor.map_comp, ← Functor.map_comp, hδ]
  split_ifs
  · rw [(Scheme.Modules.pullback i).map_id, (Scheme.Modules.pullback p).map_id]
    rfl
  · rw [Functor.map_zero, Functor.map_zero]
    rfl

/-- Original coefficient vectors give actual source elements by their five original rows. -/
def pointRows : (Fin 5 → K) →ₗ[K] PointSource K i p where
  toFun a := ∑ j : Fin 5, a j • pointRowBasis K i p g z hz j
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

omit [CharZero K] in
theorem pointCoordinate_pointRows (a : Fin 5 → K) (j : Fin 5) :
    pointCoordinate K i p j (pointRows K i p g z hz a) =
      a j • pointDualUnit K i p g z hz := by
  classical
  simp only [pointRows, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    pointCoordinate_pointRowBasis]
  simp

theorem pointRows_injective : Function.Injective (pointRows K i p g z hz) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro a ha
    change a = 0
    ext j
    have h := congrArg (pointCoordinate K i p j) ha
    rw [pointCoordinate_pointRows, map_zero] at h
    exact (smul_eq_zero.mp h).resolve_right (pointDualUnit_ne_zero K i p g z hz)
  · exact bot_le

/-- Bijectivity uses the actual original source rank five, not a given frame. -/
theorem pointRows_bijective : Function.Bijective (pointRows K i p g z hz) := by
  let hS := LagrangianFibreConormalMap.source_rank K i
  let hP := isFiniteLocallyFreeOfRank_pullback p (LagrangianFibreConormalMap.source K i) 5
  obtain ⟨hfinite, hdim⟩ := MukaiConormalFieldCoordinates.finite_and_finrank_sections K
    ((Scheme.Modules.pullback p).obj (LagrangianFibreConormalMap.source K i)) 5
  let := hfinite
  refine ⟨pointRows_injective K i p g z hz, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (pointRows_injective K i p g z hz)
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hdim.symm

/-- The actual original source has the genuine derived five-row coordinates. -/
def pointSourceEquiv : PointSource K i p ≃ₗ[K] (Fin 5 → K) :=
  (LinearEquiv.ofBijective (pointRows K i p g z hz) (pointRows_bijective K i p g z hz)).symm

theorem pointSourceEquiv_symm_apply (a : Fin 5 → K) :
    (pointSourceEquiv K i p g z hz).symm a = pointRows K i p g z hz a := rfl

end M9Native.MukaiConormalRowPointFrame

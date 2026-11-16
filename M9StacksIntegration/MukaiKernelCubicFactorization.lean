module

public import M9StacksIntegration.MukaiConormalKernelLine
public import M9StacksIntegration.MukaiKernelCubicDiagonals
public import M9StacksIntegration.MukaiClosedPointFactorization

@[expose] public section

/-! The actual kernel-restricted cubic factors through the actual
inverse determinant line in the bad generic-rank branch. Legacy
visibility is inherited only from the frozen closed-point providers.
No line-valued cubic or closed-point vanishing is supplied as a premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace M9Native.MukaiKernelCubicFactorization

open MukaiCubicCurveKernel MukaiPrimitiveCanonicalEvaluation MukaiConormalKernelLine
open MukaiBundleDeterminant MukaiTensorPullbackNaturality MukaiCubicRestriction
open MukaiKernelCubicFieldValues MukaiKernelCubicDiagonals MukaiFieldLineCubic
open MukaiCurvePointLine MukaiPointLine LagrangianMatrixChart AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0)) (d : EvaluationDiagram K f E b)
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hgen : MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X) ≤ 6)

include hσ hsemi hgen in
theorem kernelCube_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cubeObj (curveKernel K f E b d)) 1 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (curveKernel K f E b d) 1 :=
    kernel_rank_one K f E b d hσ hsemi hgen
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (tensor (curveKernel K f E b d) (curveKernel K f E b d)) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X
      (curveKernel K f E b d) (curveKernel K f E b d) 1 1
  exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X
    (tensor (curveKernel K f E b d) (curveKernel K f E b d)) (curveKernel K f E b d) 1 1

def cubicProjection : cubeObj (curveKernel K f E b d) ⟶
    dualSheaf (kernel (determinantQuotient K f E b d)) :=
  kernelCubic K f E b d ≫ pointCokernelProjection (determinantQuotient K f E b d)

include hσ hsemi hgen in
theorem pullback_cubicProjection_eq_zero (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    (Scheme.Modules.pullback p).map (cubicProjection K f E b d) = 0 := by
  let L := curveKernel K f E b d
  let hL := kernel_rank_one K f E b d hσ hsemi hgen
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 := hL
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ((Scheme.Modules.pullback p).obj L) 1 :=
    isFiniteLocallyFreeOfRank_pullback p L 1
  let P : freeOn (Spec (.of K)) 14 ⟶
      (Scheme.Modules.pullback p).obj (dualSheaf (kernel (determinantQuotient K f E b d))) :=
    (pullbackFreeIso p 14).inv ≫
      (Scheme.Modules.pullback p).map (pointCokernelProjection (determinantQuotient K f E b d))
  have hfactor : (cubePullbackIso p L).inv ≫
      (Scheme.Modules.pullback p).map (cubicProjection K f E b d) =
      pointKernelCubic K f E b d p ≫ P := by
    simp only [L, cubicProjection, pointKernelCubic, P, CategoryTheory.Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_assoc]
  have hz : (Scheme.Modules.pullback p).map (curvePointLine K f E b d) ≫
      ((pullbackFreeIso p 14).hom ≫ P) = 0 := by
    simp only [P, Iso.hom_inv_id_assoc]
    change (Scheme.Modules.pullback p).map (pointLineMap (determinantQuotient K f E b d)) ≫
      (Scheme.Modules.pullback p).map (pointCokernelProjection (determinantQuotient K f E b d)) = 0
    rw [← CategoryTheory.Functor.map_comp, pointLineMap_comp, CategoryTheory.Functor.map_zero]
  have ha : (cubePullbackIso p L).inv ≫
      (Scheme.Modules.pullback p).map (cubicProjection K f E b d) = 0 := by
    rw [hfactor]
    apply hom_eq_zero_of_diagonal K inferInstance
    intro s
    change P.app ⊤ ((pointKernelCubic K f E b d p).app ⊤
      (tripleSection K ((Scheme.Modules.pullback p).obj L) s s s)) = 0
    obtain ⟨a,hea⟩ := diagonal_pointLine_preimage K f E b d p hp s
    rw [hea]
    have hz' := congrArg (fun t => t.app ⊤ a) hz
    change P.app ⊤ ((pullbackFreeIso p 14).hom.app ⊤
      (((Scheme.Modules.pullback p).map (curvePointLine K f E b d)).app ⊤ a)) = 0 at hz'
    exact hz'
  have h := congrArg (fun a => (cubePullbackIso p L).hom ≫ a) ha
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, comp_zero] using h

include hσ hsemi hgen in
theorem closed_cubicProjection_rank_zero (x : X) (hx : IsClosed ({x} : Set X)) :
    MukaiSemiIrreducible.mapRankAt (cubicProjection K f E b d) x = 0 := by
  let : (moduleSpecΓFunctor (R := .of K)).Additive := ⟨by intro M N a b; ext z; rfl⟩
  let p := pointOfClosedPoint f x hx
  have hz := pullback_cubicProjection_eq_zero K f E b d hσ hsemi hgen p
    (pointOfClosedPoint_comp f x hx)
  have hr := FieldPointMapRank.finrank_range_pullbackSections_eq_mapRankAt K
    (cubicProjection K f E b d) p
  rw [hz, CategoryTheory.Functor.map_zero] at hr
  change finrank K (LinearMap.range (0 :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (cubeObj (curveKernel K f E b d))) →ₗ[K]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj
        (dualSheaf (kernel (determinantQuotient K f E b d)))))) = _ at hr
  rw [LinearMap.range_zero, finrank_bot] at hr
  simpa only [p, pointOfClosedPoint_apply] using hr.symm

include hσ hsemi hgen in
/-- The factor is produced by the actual kernel universal property.
The closed-point zero needed by that property is proved above. -/
theorem exists_cubic_factor :
    ∃ a : cubeObj (curveKernel K f E b d) ⟶
        dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)),
      a ≫ curvePointLine K f E b d = kernelCubic K f E b d := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  let : JacobsonSpace X := ClosedPointCurveRank.jacobsonSpace_of_curve K f
  have hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower E (3 : ℤ)) 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3
  exact MukaiClosedPointFactorization.factor_through_pointLine_of_closed_zero
    (determinantQuotient K f E b d) hQ (kernelCubic K f E b d) 1
    (kernelCube_rank K f E b d hσ hsemi hgen)
    (closed_cubicProjection_rank_zero K f E b d hσ hsemi hgen)

end M9Native.MukaiKernelCubicFactorization

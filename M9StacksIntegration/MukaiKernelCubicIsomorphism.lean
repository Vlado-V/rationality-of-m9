module

public import M9StacksIntegration.MukaiKernelCubicFactorization
public import M9StacksIntegration.FieldPointMapRankConsequences

@[expose] public section

/-! The constructed actual kernel cubic is nowhere zero on closed
fibres, hence gives an actual line-bundle isomorphism. Legacy visibility
comes only from the frozen closed-point rank-detection providers. -/

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

namespace M9Native.MukaiKernelCubicIsomorphism

open MukaiCubicCurveKernel MukaiPrimitiveCanonicalEvaluation MukaiConormalKernelLine
open MukaiKernelCubicFactorization MukaiTensorPullbackNaturality MukaiCubicRestriction
open MukaiKernelCubicFieldValues MukaiKernelCubicDiagonals MukaiFieldLineCubic
open MukaiCurvePointLine MukaiConormalFieldCoordinates

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0)) (d : EvaluationDiagram K f E b)
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (hgen : MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X) ≤ 6)

include hσ hsemi hgen in
theorem pullback_factor_ne_zero
    (a : cubeObj (curveKernel K f E b d) ⟶ dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)))
    (ha : a ≫ curvePointLine K f E b d = kernelCubic K f E b d)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    (Scheme.Modules.pullback p).map a ≠ 0 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (curveKernel K f E b d) 1 :=
    kernel_rank_one K f E b d hσ hsemi hgen
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) 1 :=
    isFiniteLocallyFreeOfRank_pullback p (curveKernel K f E b d) 1
  have hdim := finite_and_finrank_sections K ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) 1
  let : Module.Finite K (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))) := hdim.1
  let bs : Basis (Fin 1) K
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))) :=
    Module.finBasisOfFinrankEq K _ hdim.2
  have hc := diagonal_ne_zero K f E b d hσ hsemi p hp (bs 0) (bs.ne_zero 0)
  intro hazero
  have hz : (Scheme.Modules.pullback p).map (kernelCubic K f E b d) = 0 := by
    rw [← ha, CategoryTheory.Functor.map_comp, hazero, zero_comp]
  have hz' : pointKernelCubic K f E b d p = 0 := by
    simp only [pointKernelCubic, hz, comp_zero, zero_comp]
  apply hc
  rw [hz', Scheme.Modules.Hom.zero_app]
  rfl

include hσ hsemi hgen in
theorem factor_field_rank_one
    (a : cubeObj (curveKernel K f E b d) ⟶ dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)))
    (ha : a ≫ curvePointLine K f E b d = kernelCubic K f E b d)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    MukaiSemiIrreducible.mapRankAt a (p (SpecFieldStalkSections.point K)) = 1 := by
  let hC := kernelCube_rank K f E b d hσ hsemi hgen
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (cubeObj (curveKernel K f E b d)) 1 := hC
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj (cubeObj (curveKernel K f E b d))) 1 :=
    isFiniteLocallyFreeOfRank_pullback p _ 1
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      ((Scheme.Modules.pullback p).obj (cubeObj (curveKernel K f E b d))) :=
    (inferInstance : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj (cubeObj (curveKernel K f E b d))) 1).isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower E (3 : ℤ)) 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ))) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf _ 1 inferInstance
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj (dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)))) 1 :=
    isFiniteLocallyFreeOfRank_pullback p _ 1
  let : Epi ((Scheme.Modules.pullback p).map a) :=
    SectionCokernelLocallyFree.epi_of_ne_zero_to_rank_one K _
      (pullback_factor_ne_zero K f E b d hσ hsemi hgen a ha p hp)
  have hsurj := MukaiLagrangianMap.inducedFiberMap_surjective ((Scheme.Modules.pullback p).map a)
    (SpecFieldStalkSections.point K)
  have hr : MukaiSemiIrreducible.mapRankAt ((Scheme.Modules.pullback p).map a)
      (SpecFieldStalkSections.point K) = 1 := by
    change finrank ((Spec (.of K)).residueField (SpecFieldStalkSections.point K))
      (LinearMap.range (TupleEvaluationFiber.inducedFiberMap ((Scheme.Modules.pullback p).map a)
        (SpecFieldStalkSections.point K))) = 1
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    exact TupleEvaluationFiber.finrank_fiber _ 1 _
  exact (FieldPointMapRankConsequences.mapRankAt_pullback K a p).symm.trans hr

include hσ hsemi hgen in
theorem factor_isIso
    (a : cubeObj (curveKernel K f E b d) ⟶ dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)))
    (ha : a ≫ curvePointLine K f E b d = kernelCubic K f E b d) : IsIso a := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  let : JacobsonSpace X := ClosedPointCurveRank.jacobsonSpace_of_curve K f
  have hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ))) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf _ 1
      (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3)
  apply MukaiClosedPointFactorization.isIso_of_closedRank_one a
    (kernelCube_rank K f E b d hσ hsemi hgen) hD
  intro x hx
  simpa only [pointOfClosedPoint_apply] using factor_field_rank_one K f E b d hσ hsemi hgen a ha
    (pointOfClosedPoint f x hx) (pointOfClosedPoint_comp f x hx)

include hσ hsemi hgen in
theorem exists_cubic_iso :
    ∃ e : cubeObj (curveKernel K f E b d) ≅ dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ)),
      e.hom ≫ curvePointLine K f E b d = kernelCubic K f E b d := by
  obtain ⟨a,ha⟩ := exists_cubic_factor K f E b d hσ hsemi hgen
  let : IsIso a := factor_isIso K f E b d hσ hsemi hgen a ha
  exact ⟨asIso a,ha⟩

end M9Native.MukaiKernelCubicIsomorphism

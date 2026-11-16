module

public import M9StacksIntegration.MukaiConstantPointSections
public import M9StacksIntegration.MukaiCurvePointCoordinates
public import M9StacksIntegration.FieldPointMapRank

/-! The actual conormal evaluation at a same-base field point is the
original primitive evaluation composed with the original field-point
conormal map. All changes of coordinates below are genuine native
pullback/free-section comparisons. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.MukaiCurveEvaluationPoint

open MukaiPrimitiveCanonicalEvaluation MukaiCubicCurveKernel MukaiCubicFreeSheaf
open MukaiCubicConstantSheaf MukaiConstantPointSections MukaiConstantLinearCoordinates
open MukaiCurvePointCoordinates MukaiConormalFieldCoordinates MukaiConormalOriginCoordinates
open LagrangianMatrixChart AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

theorem formsIso_inv_point (s : moduleSpecΓFunctor.obj
    ((Scheme.Modules.pullback p).obj (freeOn X 14))) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (formsIso K f).inv)).hom s =
      pointConstantEquiv K f p hp (formModule K)
        ((formsCoordinates K).symm ((freeCoordinates K 14)
          ((moduleSpecΓFunctor.map (pullbackFreeIso p 14).hom).hom s))) := by
  apply (pointBasisEquiv K f p (formModule K) 14 (formsBasis K)).injective
  change (freeCoordinates K 14)
      ((pullbackFreeIso p 14).hom.app ⊤
        (((Scheme.Modules.pullback p).map (formsIso K f).hom).app ⊤
          (((Scheme.Modules.pullback p).map (formsIso K f).inv).app ⊤ s))) = _
  have hc := congrArg (fun a => a.app ⊤ s)
    ((Scheme.Modules.pullback p).mapIso (formsIso K f)).inv_hom_id
  change ((Scheme.Modules.pullback p).map (formsIso K f).hom).app ⊤
    (((Scheme.Modules.pullback p).map (formsIso K f).inv).app ⊤ s) = s at hc
  rw [hc]
  change _ = pointBasisEquiv K f p (formModule K) 14 (formsBasis K)
    (pointConstantSection K f p hp (formModule K) _)
  rw [pointBasisEquiv_section]
  change _ = formsCoordinates K ((formsCoordinates K).symm _)
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (E : X.Modules) (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

theorem forms_constant_point (s : PointSource K f E b d p) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (curveFormMap K f E b d ≫ (formsIso K f).inv))).hom s =
      pointConstantEquiv K f p hp (formModule K) (pointFormsMap K f E b d p s) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact formsIso_inv_point K f p hp _

variable [IsProper f] [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

local instance determinantH0_finite_instance : FiniteDimensional K (DeterminantH0 K f E) :=
  determinantH0_finite K f E

/-- This is the actual original evaluation map on pulled sections;
the target comparison is the genuine constant-module field-point iso. -/
theorem curveEvaluationMap_point (s : PointSource K f E b d p) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (curveEvaluationMap K f E b d))).hom s =
      pointConstantEquiv K f p hp (ModuleCat.of K (DeterminantH0 K f E))
        (primitiveEvaluation K f E b (pointFormsMap K f E b d p s)) := by
  have hn := pointConstantSection_naturality K f p hp (evaluationModuleMap K f E b)
    (pointFormsMap K f E b d p s)
  change (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      ((curveFormMap K f E b d ≫ (formsIso K f).inv) ≫
        constantMap (.of K) f (evaluationModuleMap K f E b)))).hom s = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  change (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (constantMap (.of K) f (evaluationModuleMap K f E b)))).hom
    ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (curveFormMap K f E b d ≫ (formsIso K f).inv))).hom s) = _
  rw [forms_constant_point K f p hp E b d]
  exact hn

theorem curveEvaluationMap_point_linear :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (curveEvaluationMap K f E b d))).hom =
      (pointConstantEquiv K f p hp (ModuleCat.of K (DeterminantH0 K f E))).toLinearMap.comp
        ((primitiveEvaluation K f E b).comp (pointFormsMap K f E b d p)) := by
  ext s
  exact curveEvaluationMap_point K f p hp E b d s

include hp in
/-- Original residue rank, computed using the original primitive
evaluation on the genuine field-point conormal image. -/
theorem mapRankAt_eq_finrank_evaluation :
    MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d)
      (p (SpecFieldStalkSections.point K)) =
      finrank K (LinearMap.range ((primitiveEvaluation K f E b).comp
        (pointFormsMap K f E b d p))) := by
  rw [← FieldPointMapRank.finrank_range_pullbackSections_eq_mapRankAt K
    (curveEvaluationMap K f E b d) p, curveEvaluationMap_point_linear K f p hp E b d]
  simpa only [LinearMap.comp_id, LinearEquiv.refl_toLinearMap] using
    FieldBaseChangeRank.finrank_range_equiv K
      ((primitiveEvaluation K f E b).comp (pointFormsMap K f E b d p))
      (LinearEquiv.refl K _) (pointConstantEquiv K f p hp (ModuleCat.of K (DeterminantH0 K f E)))

include hp in
theorem kernelFormsMap_mem_evaluationKernel
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))) :
    primitiveEvaluation K f E b (kernelFormsMap K f E b d p s) = 0 := by
  let : (moduleSpecΓFunctor (R := .of K)).Additive := ⟨by intro M N a b; ext x; rfl⟩
  have hz : (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (curveEvaluationMap K f E b d))).hom
      ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
        (kernel.ι (curveEvaluationMap K f E b d)))).hom s) = 0 := by
    have h := congrArg (fun a => (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback p).map a)).hom s)
      (kernel.condition (curveEvaluationMap K f E b d))
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
    exact h.trans (by simp only [CategoryTheory.Functor.map_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply])
  rw [curveEvaluationMap_point K f p hp E b d] at hz
  exact (pointConstantEquiv K f p hp (ModuleCat.of K (DeterminantH0 K f E))).injective
    (hz.trans (map_zero _).symm)

end M9Native.MukaiCurveEvaluationPoint

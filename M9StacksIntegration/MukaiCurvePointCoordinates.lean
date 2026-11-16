module

public import M9StacksIntegration.MukaiCubicCurveKernel
public import M9StacksIntegration.MukaiConormalFieldCoordinates

/-! The genuine twice-pulled curve conormal inclusion agrees with the
original field-point inclusion through the native pullback composition
comparison. This only aligns the original morphisms; it specifies no
conormal image or first-jet kernel. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace M9Native.MukaiCurvePointCoordinates

open MukaiCubicCurveKernel MukaiPrimitiveCanonicalEvaluation MukaiConormalBundle
open MukaiConormalEulerTwist MukaiConormalFieldCoordinates MukaiConormalOriginCoordinates
open LagrangianMatrixChart AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

def sourcePointIso (p : Spec (.of K) ⟶ X) :
    (Scheme.Modules.pullback p).obj (curveSource K f E b d) ≅
      (Scheme.Modules.pullback (p ≫ d.map)).obj (twistedConormal K) :=
  (Scheme.Modules.pullbackComp p d.map).app (twistedConormal K)

omit [IsAlgClosed K] in
theorem curveFormMap_pullback (p : Spec (.of K) ⟶ X) :
    (Scheme.Modules.pullback p).map (curveFormMap K f E b d) ≫ (pullbackFreeIso p 14).hom =
      (sourcePointIso K f E b d p).hom ≫
        (Scheme.Modules.pullback (p ≫ d.map)).map (twistedConormalMap K) ≫
          (pullbackFreeIso (p ≫ d.map) 14).hom := by
  change (Scheme.Modules.pullback p).map
      ((Scheme.Modules.pullback d.map).map (twistedConormalMap K) ≫
        (pullbackFreeIso d.map 14).hom) ≫ (pullbackFreeIso p 14).hom = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← pullbackFreeIso_comp d.map p 14]
  have hn :
      (Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullback d.map).map (twistedConormalMap K)) ≫
        (Scheme.Modules.pullbackComp p d.map).hom.app
          (freeOn (LagrangianGrassmannian.space K) 14) =
      (Scheme.Modules.pullbackComp p d.map).hom.app (twistedConormal K) ≫
        (Scheme.Modules.pullback (p ≫ d.map)).map (twistedConormalMap K) :=
    (Scheme.Modules.pullbackComp p d.map).hom.naturality (twistedConormalMap K)
  simpa only [sourcePointIso, Category.assoc, Iso.app_hom, freeOn] using
    congrArg (fun a => a ≫ (pullbackFreeIso (p ≫ d.map) 14).hom) hn

abbrev PointSource (p : Spec (.of K) ⟶ X) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveSource K f E b d))

def sourcePointEquiv (p : Spec (.of K) ⟶ X) :
    PointSource K f E b d p ≃ₗ[K] Source K (p ≫ d.map) :=
  (moduleSpecΓFunctor.mapIso (sourcePointIso K f E b d p)).toLinearEquiv

def pointFormsMap (p : Spec (.of K) ⟶ X) :
    PointSource K f E b d p →ₗ[K] MukaiPrimitiveQuartic.Forms K :=
  (formsCoordinates K).symm.toLinearMap.comp ((freeCoordinates K 14).toLinearMap.comp
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (curveFormMap K f E b d) ≫
      (pullbackFreeIso p 14).hom)).hom)

omit [IsAlgClosed K] in
theorem pointFormsMap_eq (p : Spec (.of K) ⟶ X) :
    pointFormsMap K f E b d p =
      (formsMap K (p ≫ d.map)).comp (sourcePointEquiv K f E b d p).toLinearMap := by
  have hs :
      (Scheme.Modules.pullback p).map (curveFormMap K f E b d) ≫ (pullbackFreeIso p 14).hom =
      (sourcePointIso K f E b d p).hom ≫
        ((Scheme.Modules.pullback (p ≫ d.map)).map (twistedConormalMap K) ≫
          (pullbackFreeIso (p ≫ d.map) 14).hom) := by
    simpa only [Category.assoc] using curveFormMap_pullback K f E b d p
  have hΓ :
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (curveFormMap K f E b d) ≫
        (pullbackFreeIso p 14).hom)).hom =
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback (p ≫ d.map)).map (twistedConormalMap K) ≫
        (pullbackFreeIso (p ≫ d.map) 14).hom)).hom.comp
        (moduleSpecΓFunctor.map (sourcePointIso K f E b d p).hom).hom := by
    have hh := congrArg (fun a => moduleSpecΓFunctor.map a) hs
    rw [CategoryTheory.Functor.map_comp] at hh
    exact congrArg ModuleCat.Hom.hom hh
  unfold pointFormsMap
  rw [hΓ]
  rfl

theorem pointFormsMap_injective (p : Spec (.of K) ⟶ X) :
    Function.Injective (pointFormsMap K f E b d p) := by
  rw [pointFormsMap_eq]
  exact (formsMap_injective K (p ≫ d.map)).comp (sourcePointEquiv K f E b d p).injective

theorem pointSource_finite_and_finrank (p : Spec (.of K) ⟶ X) :
    Module.Finite K (PointSource K f E b d p) ∧
      finrank K (PointSource K f E b d p) = 7 := by
  let := curveSource_rank K f E b d
  let := isFiniteLocallyFreeOfRank_pullback p (curveSource K f E b d) 7
  exact finite_and_finrank_sections K _ 7

theorem finrank_range_pointFormsMap (p : Spec (.of K) ⟶ X) :
    finrank K (LinearMap.range (pointFormsMap K f E b d p)) = 7 :=
  (LinearMap.finrank_range_of_inj (pointFormsMap_injective K f E b d p)).trans
    (pointSource_finite_and_finrank K f E b d p).2

def kernelFormsMap (p : Spec (.of K) ⟶ X) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) →ₗ[K]
      MukaiPrimitiveQuartic.Forms K :=
  (pointFormsMap K f E b d p).comp
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (kernel.ι (curveEvaluationMap K f E b d)))).hom

omit [IsAlgClosed K] in
theorem range_kernelFormsMap_le (p : Spec (.of K) ⟶ X) :
    LinearMap.range (kernelFormsMap K f E b d p) ≤ LinearMap.range (pointFormsMap K f E b d p) :=
  LinearMap.range_comp_le_range _ _

variable [IsCurve K f] [Smooth f] [IsProper f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

theorem pullback_curveKernel_inclusion_mono (p : Spec (.of K) ⟶ X) :
    Mono ((Scheme.Modules.pullback p).map (kernel.ι (curveEvaluationMap K f E b d))) := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (CurveKernelImage.sequence (curveEvaluationMap K f E b d)).X₃ := by
    change SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image (curveEvaluationMap K f E b d))
    exact curveImage_isFiniteLocallyFree K f E b d
  exact (Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree p
    (CurveKernelImage.sequence (curveEvaluationMap K f E b d))
    (CurveKernelImage.sequence_shortExact (curveEvaluationMap K f E b d))).mono_f

theorem kernelFormsMap_injective (p : Spec (.of K) ⟶ X) :
    Function.Injective (kernelFormsMap K f E b d p) := by
  let : Mono ((Scheme.Modules.pullback p).map (kernel.ι (curveEvaluationMap K f E b d))) :=
    pullback_curveKernel_inclusion_mono K f E b d p
  let : (moduleSpecΓFunctor (R := .of K)).IsRightAdjoint :=
    (tilde.adjunction (R := .of K)).isRightAdjoint
  have hi : Function.Injective (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (kernel.ι (curveEvaluationMap K f E b d)))).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact (pointFormsMap_injective K f E b d p).comp hi

end M9Native.MukaiCurvePointCoordinates

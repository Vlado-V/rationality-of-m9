module

public import M9StacksIntegration.MukaiCubicRestriction
public import M9StacksIntegration.MukaiCurvePointCoordinates
public import M9StacksIntegration.MukaiFieldLineCubic

/-! Actual diagonal values of the original kernel-restricted cubic.
The input coefficient is the original field-point categorical-kernel
map, with the genuine pullback/free/tensor comparisons retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace M9Native.MukaiKernelCubicFieldValues

open MukaiPrimitiveCanonicalEvaluation MukaiCubicCurveKernel MukaiCubicRestriction
open MukaiCurvePointCoordinates MukaiCubicFreeSheaf MukaiConormalFieldCoordinates
open MukaiConormalOriginCoordinates MukaiFreePullbackCoordinates MukaiTensorPullbackNaturality
open MukaiBundleDeterminant LinearIncidenceTensorCoordinates MukaiFieldLineCubic
open LagrangianMatrixChart AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K]

theorem freeCoordinates_formSection (ell : MukaiPrimitiveQuartic.Forms K) :
    freeCoordinates K 14 (formSection K (𝟙 (Spec (.of K))) ell) = formsCoordinates K ell := by
  ext j
  change (Scheme.ΓSpecIso (.of K)).hom
    (freeSectionCoordinates (Spec (.of K)) 14 (formSection K (𝟙 (Spec (.of K))) ell) j) = _
  rw [formSection_coordinates, baseScalar_id, Iso.inv_hom_id_apply, formsCoordinates_apply]

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0)) (d : EvaluationDiagram K f E b)

def pointKernelMap (p : Spec (.of K) ⟶ X) :
    (Scheme.Modules.pullback p).obj (curveKernel K f E b d) ⟶ freeOn (Spec (.of K)) 14 :=
  pointMap p (kernelToFree K f E b d)

theorem pointKernelMap_formCoordinates (p : Spec (.of K) ⟶ X)
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))) :
    (formsCoordinates K).symm ((freeCoordinates K 14)
      ((moduleSpecΓFunctor.map (pointKernelMap K f E b d p)).hom s)) =
        kernelFormsMap K f E b d p s := by
  unfold pointKernelMap pointMap kernelToFree kernelFormsMap pointFormsMap
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

theorem pointKernelMap_section (p : Spec (.of K) ⟶ X)
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))) :
    (pointKernelMap K f E b d p).app ⊤ s =
      formSection K (𝟙 (Spec (.of K))) (kernelFormsMap K f E b d p s) := by
  apply (freeCoordinates K 14).injective
  change (freeCoordinates K 14)
    ((moduleSpecΓFunctor.map (pointKernelMap K f E b d p)).hom s) = _
  rw [freeCoordinates_formSection]
  have h := congrArg (formsCoordinates K) (pointKernelMap_formCoordinates K f E b d p s)
  simpa only [LinearEquiv.apply_symm_apply] using h

def pointKernelCubic (p : Spec (.of K) ⟶ X) :
    cubeObj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) ⟶
      freeOn (Spec (.of K)) 14 :=
  (cubePullbackIso p (curveKernel K f E b d)).inv ≫
    (Scheme.Modules.pullback p).map (kernelCubic K f E b d) ≫ (pullbackFreeIso p 14).hom

theorem pointKernelCubic_diagonal (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))) :
    (pointKernelCubic K f E b d p).app ⊤
      (tripleSection K ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) s s s) =
      dualFormSection K (𝟙 (Spec (.of K)))
        (MukaiPrimitiveQuartic.primitiveCubic K (kernelFormsMap K f E b d p s)
          (kernelFormsMap K f E b d p s) (kernelFormsMap K f E b d p s)) := by
  have h : pointKernelCubic K f E b d p =
      cubeMap (pointKernelMap K f E b d p) ≫ cubicFreeMap K (𝟙 (Spec (.of K))) :=
    kernelCubic_fieldPoint K f E b d p hp
  rw [h]
  change (cubicFreeMap K (𝟙 (Spec (.of K)))).app ⊤
    ((cubeMap (pointKernelMap K f E b d p)).app ⊤
      (tensorTop (Spec (.of K))
        (tensor ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))
          ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)))
        ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))
        (tensorTop (Spec (.of K)) ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))
          ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) s s) s)) = _
  simp only [cubeMap_tensorTop, pointKernelMap_section]
  rw [cubicFreeMap_section]

end M9Native.MukaiKernelCubicFieldValues

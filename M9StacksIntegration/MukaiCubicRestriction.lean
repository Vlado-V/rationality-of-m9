module

public import M9StacksIntegration.MukaiCubicFreePullback
public import M9StacksIntegration.MukaiCubicCurveKernel

/-! Restrict the original global cubic to an actual sheaf map into the
fourteen-coordinate bundle. Its field-point restriction is the original
coefficient cubic on the original pulled map. In particular the curve
kernel cubic below is constructed from the genuine categorical kernel. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiCubicRestriction

open MukaiBundleDeterminant MukaiTensorPullbackNaturality MukaiCubicFreeSheaf
open MukaiCubicFreePullback LagrangianMatrixChart AlgebraicGeometry.Grassmannian
open LinearIncidenceTensorCoordinates

variable {X Y : Scheme.{u}}

theorem cubeMap_comp {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C) :
    cubeMap (a ≫ b) = cubeMap a ≫ cubeMap b := by
  simp only [cubeMap, tensorMap_comp]

theorem freeCubePullbackIso_hom (p : Y ⟶ X) :
    (freeCubePullbackIso p).hom =
      (cubePullbackIso p (freeOn X 14)).hom ≫ cubeMap (pullbackFreeIso p 14).hom := rfl

variable (K : Type u) [Field K] [CharZero K] (f : X ⟶ Spec (.of K))

def restrictCubic {A : X.Modules} (a : A ⟶ freeOn X 14) : cubeObj A ⟶ freeOn X 14 :=
  cubeMap a ≫ cubicFreeMap K f

def pointMap {A : X.Modules} (p : Y ⟶ X) (a : A ⟶ freeOn X 14) :
    (Scheme.Modules.pullback p).obj A ⟶ freeOn Y 14 :=
  (Scheme.Modules.pullback p).map a ≫ (pullbackFreeIso p 14).hom

theorem pointMap_cube_square {A : X.Modules} (p : Y ⟶ X) (a : A ⟶ freeOn X 14) :
    (Scheme.Modules.pullback p).map (cubeMap a) ≫ (freeCubePullbackIso p).hom =
      (cubePullbackIso p A).hom ≫ cubeMap (pointMap p a) := by
  rw [freeCubePullbackIso_hom, ← Category.assoc, cubePullbackIso_naturality,
    Category.assoc, ← cubeMap_comp]
  rfl

theorem pointMap_cube_inverse_square {A : X.Modules} (p : Y ⟶ X) (a : A ⟶ freeOn X 14) :
    (cubePullbackIso p A).inv ≫ (Scheme.Modules.pullback p).map (cubeMap a) =
      cubeMap (pointMap p a) ≫ (freeCubePullbackIso p).inv := by
  apply (cancel_mono (freeCubePullbackIso p).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [pointMap_cube_square, Iso.inv_hom_id_assoc]

theorem restrictCubic_pullback {A : X.Modules} (p : Y ⟶ X) (a : A ⟶ freeOn X 14) :
    (cubePullbackIso p A).inv ≫
      (Scheme.Modules.pullback p).map (restrictCubic K f a) ≫ (pullbackFreeIso p 14).hom =
      cubeMap (pointMap p a) ≫ pulledCubicMap K f p := by
  unfold restrictCubic pulledCubicMap
  rw [CategoryTheory.Functor.map_comp]
  simp only [← Category.assoc]
  rw [pointMap_cube_inverse_square]

theorem restrictCubic_fieldPoint {A : X.Modules} (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (a : A ⟶ freeOn X 14) :
    (cubePullbackIso p A).inv ≫
      (Scheme.Modules.pullback p).map (restrictCubic K f a) ≫ (pullbackFreeIso p 14).hom =
      cubeMap (pointMap p a) ≫ cubicFreeMap K (𝟙 (Spec (.of K))) := by
  rw [restrictCubic_pullback, pulledCubicMap_fieldPoint K f p hp]

variable (E : X.Modules) (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : MukaiPrimitiveCanonicalEvaluation.EvaluationDiagram K f E b)

def kernelToFree : MukaiCubicCurveKernel.curveKernel K f E b d ⟶ freeOn X 14 :=
  kernel.ι (MukaiCubicCurveKernel.curveEvaluationMap K f E b d) ≫
    MukaiCubicCurveKernel.curveFormMap K f E b d

def kernelCubic : cubeObj (MukaiCubicCurveKernel.curveKernel K f E b d) ⟶ freeOn X 14 :=
  restrictCubic K f (kernelToFree K f E b d)

theorem kernelCubic_fieldPoint (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    (cubePullbackIso p (MukaiCubicCurveKernel.curveKernel K f E b d)).inv ≫
      (Scheme.Modules.pullback p).map (kernelCubic K f E b d) ≫ (pullbackFreeIso p 14).hom =
      cubeMap (pointMap p (kernelToFree K f E b d)) ≫ cubicFreeMap K (𝟙 (Spec (.of K))) :=
  restrictCubic_fieldPoint K f p hp (kernelToFree K f E b d)

end M9Native.MukaiCubicRestriction

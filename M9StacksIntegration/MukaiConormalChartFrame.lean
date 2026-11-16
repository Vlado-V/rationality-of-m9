module

public import M9StacksIntegration.MukaiConormalChartJets
public import M9StacksIntegration.LineFramePullback
public import M9StacksIntegration.LagrangianPluckerGeneration
public import M9StacksIntegration.LagrangianProjectiveRatio

/-! The actual determinant frame on a genuine LG chart induces actual
projective and field-point frames, retaining all original fourteen sections. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.MukaiConormalChartFrame

open LagrangianGrassmannian LagrangianPluckerQuotient MukaiConormalChartJets

variable (K : Type u) [Field K] [CharZero K]
variable (f : chart K ⟶ space K)
variable (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅
  SheafOfModules.unit (chart K).ringCatSheaf)

abbrev projectiveMap : chart K ⟶ projectiveSpaceAtUniverse.{u} 13 :=
  f ≫ LagrangianPlucker.integralPrimitivePlucker K

abbrev PositiveLine := Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13

def sectionTuple (j : Fin 14) : Γ(chart K,⊤) :=
  e.hom.app ⊤ (pullbackGlobalSections f (determinantLine K) (primitiveSections K j))

/-- The source frame uses the exact pinned hyperplane/determinant iso. -/
def positiveFrame : (Scheme.Modules.pullback (projectiveMap K f)).obj PositiveLine ≅
    SheafOfModules.unit (chart K).ringCatSheaf :=
  LagrangianProjectiveRatio.positiveLineIso K f ≪≫ e

/-- All native homogeneous coordinates retain the original tuple. -/
theorem positiveFrame_coordinate (j : Fin 14) :
    (positiveFrame K f e).hom.app ⊤
      (Stacks.TwistPullbackPinned.pullbackCoordSection (projectiveMap K f) j) =
        sectionTuple K f e j := by
  change e.hom.app ⊤
    ((LagrangianProjectiveRatio.positiveLineIso K f).hom.app ⊤
      (Stacks.TwistPullbackPinned.pullbackCoordSection (projectiveMap K f) j)) = _
  rw [LagrangianProjectiveRatio.positiveLineIso_coordinate]
  rfl

/-- The actual field-point determinant frame is constructed by pullback;
no separate choice or compatibility equation is supplied. -/
def pointDeterminantFrame (z : Spec (.of K) ⟶ chart K) :
    (Scheme.Modules.pullback (z ≫ f)).obj (determinantLine K) ≅
      SheafOfModules.unit (Spec (.of K)).ringCatSheaf :=
  ((Scheme.Modules.pullbackComp z f).app (determinantLine K)).symm ≪≫
    LineFramePullback.pullbackFrame z ((Scheme.Modules.pullback f).obj (determinantLine K)) e

theorem pointDeterminantFrame_coordinate (z : Spec (.of K) ⟶ chart K) (j : Fin 14) :
    (pointDeterminantFrame K f e z).hom.app ⊤
      (pullbackGlobalSections (z ≫ f) (determinantLine K) (primitiveSections K j)) =
        z.appTop (sectionTuple K f e j) := by
  change LinearIncidenceTensorCoordinates.unitCoordinate (Spec (.of K))
    ((LineFramePullback.pullbackFrame z ((Scheme.Modules.pullback f).obj
      (determinantLine K)) e).hom.app ⊤
        (((Scheme.Modules.pullbackComp z f).inv.app (determinantLine K)).app ⊤
          (pullbackGlobalSections (z ≫ f) (determinantLine K) (primitiveSections K j)))) = _
  rw [LineFramePullback.pullbackComp_inv_apply, LineFramePullback.pullbackFrame_coordinate]
  rfl

end M9Native.MukaiConormalChartFrame

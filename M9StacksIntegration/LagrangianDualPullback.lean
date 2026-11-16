module

public import M9StacksIntegration.LagrangianDualCoefficients
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeNaturality

/-! The actual dual base-change comparison and its original evaluation formula. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.LagrangianDualPullback

open Stacks.AlgebraicGeometry.ReflexiveModules RingedSpaceModuleAdjunction

variable {X Y : Scheme.{u}}

/-- The actual dual base-change comparison is invertible for an actual
finite locally free sheaf; its isomorphism property is derived natively. -/
def dualPullbackIso (g : X ⟶ Y) (F : Y.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFree F) :
    (Scheme.Modules.pullback g).obj (dualSheaf F) ≅
      dualSheaf ((Scheme.Modules.pullback g).obj F) := by
  letI : IsIso (Stacks.Chow.pullbackDualMap g F) :=
    Stacks.Chow.pullbackDualMap_isIso g F hF
  exact asIso (Stacks.Chow.pullbackDualMap g F)

/-- Pairing the actual pullbacks of a dual section and a section is
the actual pullback of their original evaluation. -/
theorem dualPullback_evaluation_unit (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (α : (dualSheaf F).val.obj (op U)) (m : F.val.obj (op U)) :
    (((Stacks.Chow.pullbackDualMap g F).val.app (op (g ⁻¹ᵁ U))
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
        (dualSheaf F)).val.app (op U) α)).app
          (op (Over.mk (𝟙 (g ⁻¹ᵁ U))))).hom
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F).val.app
        (op U) m)=
      (g.app U).hom ((α.app (op (Over.mk (𝟙 U)))).hom m) :=
  (Stacks.Chow.pullbackDualMap_eval g F (g ⁻¹ᵁ U) _ _).trans
    (Stacks.Chow.pullbackEvaluation_unit_tmul g F U α m)

end M9Native.LagrangianDualPullback

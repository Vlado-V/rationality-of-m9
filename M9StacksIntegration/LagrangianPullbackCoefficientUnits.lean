module

public import M9StacksIntegration.LagrangianIsotropicRestriction
public import M9StacksIntegration.LagrangianDualPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections

/-! Literal local coefficient functions under the actual pullback unit. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace M9Native.LagrangianPullbackCoefficientUnits

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianIsotropicRestriction LagrangianDualPullback
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X Y : Scheme.{u}} {Q : Y.Modules}

/-- The original quotient basis sections pull back to their literal
actual unit images on every open, with no frame-choice premise. -/
theorem quotientVector_pullback_unit (g : X ⟶ Y) (q : freeOn Y 6 ⟶ Q)
    (U : Y.Opens) (j : Fin 6) :
    quotientVector (pulledQuotient g q) (g ⁻¹ᵁ U) j=
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Q).val.app (op U))
        (quotientVector q U j) := by
  let P := (Scheme.Modules.pullback g).obj Q
  let η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Q
  have hb : (pulledQuotient g q).app ⊤ (freeVector X j)=
      η.app ⊤ (q.app ⊤ (freeVector Y j)) :=
    (pulledQuotient_basis g q j).trans
      (ConcreteCategory.congr_hom (pullbackGlobalSections_eq_unit g Q)
        (q.app ⊤ (freeVector Y j)))
  have hn : P.presheaf.map (homOfLE (show g ⁻¹ᵁ U≤⊤ from le_top)).op
      (η.app ⊤ (q.app ⊤ (freeVector Y j)))=
    η.app U (Q.presheaf.map (homOfLE (show U≤⊤ from le_top)).op
      (q.app ⊤ (freeVector Y j))) :=
    (ConcreteCategory.congr_hom
      (η.val.naturality (homOfLE (show U≤⊤ from le_top)).op)
      (q.app ⊤ (freeVector Y j))).symm
  exact (congrArg (fun z : Γ(P,⊤) =>
    P.presheaf.map (homOfLE (show g ⁻¹ᵁ U≤⊤ from le_top)).op z) hb).trans hn

/-- The actual coefficients of a pulled-back dual section are the
actual structure-map images of its original coefficient functions. -/
theorem coefficientMap_pullback_unit (g : X ⟶ Y) (q : freeOn Y 6 ⟶ Q)
    (U : Y.Opens) (α : Γ(dualSheaf Q,U)) (j : Fin 6) :
    coefficientMap (pulledQuotient g q) (g ⁻¹ᵁ U)
      ((Stacks.Chow.pullbackDualMap g Q).val.app (op (g ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (dualSheaf Q)).val.app (op U) α)) j=
      (g.app U).hom (coefficientMap q U α j) := by
  change evalAt ((Scheme.Modules.pullback g).obj Q)
    ((Stacks.Chow.pullbackDualMap g Q).val.app (op (g ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (dualSheaf Q)).val.app (op U) α))
      (quotientVector (pulledQuotient g q) (g ⁻¹ᵁ U) j)=_
  rw [quotientVector_pullback_unit]
  exact dualPullback_evaluation_unit g Q U α (quotientVector q U j)

end M9Native.LagrangianPullbackCoefficientUnits

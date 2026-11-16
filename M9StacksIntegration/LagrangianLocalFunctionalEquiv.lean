module

public import M9StacksIntegration.LagrangianLocalIsotropy
public import Mathlib.CategoryTheory.HomCongr

/-! Actual local dual sections and actual functionals on the open subscheme. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianLocalFunctionalEquiv

open LagrangianDualCoefficients
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- This is the actual sheaf Hom carried by the definition of a local
section of the original dual, with no local-freeness assumption. -/
def sectionOverMorphismEquiv (Q : X.Modules) (U : X.Opens) :
    Γ(dualSheaf Q,U) ≃ (Q.over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U) where
  toFun α := ⟨α⟩
  invFun f := f.val
  left_inv _ := rfl
  right_inv f := by cases f; rfl

/-- The original local-functional construction is a genuine bijection
onto all actual functionals on the literal open subscheme. -/
def localFunctionalEquiv (Q : X.Modules) (U : X.Opens) :
    Γ(dualSheaf Q,U) ≃
      (Q.restrict U.ι ⟶ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :=
  (sectionOverMorphismEquiv Q U).trans
    (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv |>.trans
      (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app Q)
        (((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)) ≪≫
          Scheme.Modules.restrictUnitIso U.ι))

@[simp] theorem localFunctionalEquiv_apply (Q : X.Modules) (U : X.Opens)
    (α : Γ(dualSheaf Q,U)) : localFunctionalEquiv Q U α=localFunctional Q U α := rfl

/-- In particular every genuine frame functional on an open is induced
by a section of the original dual sheaf. -/
theorem localFunctional_surjective (Q : X.Modules) (U : X.Opens) :
    Function.Surjective (localFunctional Q U) :=
  (localFunctionalEquiv Q U).surjective

end M9Native.LagrangianLocalFunctionalEquiv

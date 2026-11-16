module

public import M9StacksIntegration.LagrangianIsotropicDual
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictOpenSections

/-! Exact open-section transports for the intrinsic LG cotangent map. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianLocalIsotropy

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients LagrangianIsotropicDual
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- An actual sheaf morphism gives the corresponding actual global
dual section, by restriction on every open. -/
def functionalSection (Q : X.Modules) (a : Q ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Γ(dualSheaf Q,⊤) :=
  { app := fun W => a.val.app (op W.unop.left)
    naturality := by
      intro U V f
      exact a.val.naturality f.unop.left.op }

@[simp] theorem evalAt_functionalSection (Q : X.Modules)
    (a : Q ⟶ SheafOfModules.unit X.ringCatSheaf) (s : Γ(Q,⊤)) :
    evalAt Q (functionalSection Q a) s=a.app ⊤ s := rfl

/-- The original local functional transported to the actual open
subscheme evaluates exactly as the original section of the dual. -/
theorem localFunctional_top_evaluation (Q : X.Modules) (U : X.Opens)
    (α : Γ(dualSheaf Q,U)) (s : Γ(Q.restrict U.ι,⊤)) :
    (Scheme.Opens.topIso U).hom ((localFunctional Q U α).app ⊤ s)=
      evalAt Q α ((openSectionsIso Q U).hom s) := by
  let W : Over U := Over.mk (homOfLE (show U.ι ''ᵁ ⊤≤U from le_of_eq U.ι_image_top))
  let g : Over.mk (𝟙 U) ⟶ W :=
    Over.homMk (eqToHom U.ι_image_top.symm) (Subsingleton.elim _ _)
  simp only [localFunctional, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.restrictUnitIso, Scheme.Modules.overFunctorEquiv, Scheme.Modules.overEquiv,
    Scheme.Opens.ι_appIso]
  change X.presheaf.map (eqToHom U.ι_image_top.symm).op
      (dualPairing Q α W ((Q.restrictAppIso U.ι ⊤).hom s))=
    dualPairing Q α (Over.mk (𝟙 U))
      (Q.presheaf.map (eqToHom U.ι_image_top.symm).op ((Q.restrictAppIso U.ι ⊤).hom s))
  exact (dualPairing_naturality Q α g _).symm

end M9Native.LagrangianLocalIsotropy

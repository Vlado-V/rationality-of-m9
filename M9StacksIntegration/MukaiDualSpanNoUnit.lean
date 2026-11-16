module

public import M9StacksIntegration.MukaiDualSpanDual
public import M9StacksIntegration.MukaiBundleUniqueness

/-!
# The actual dual span has no quotient to the structure sheaf

The checked dual-span dual has no sections. The actual sheaf-Hom/global
section equivalence transports that statement to morphisms from the
original dual span to the structure sheaf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle

universe u

namespace M9Native.MukaiDualSpanSections

variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem hom_structure_subsingleton_of_complete_net
    (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f α 0))
    (hgen : Epi (netEvaluation α (completeNetSections f α b))) :
    Subsingleton (dualSpan α (completeNetSections f α b) ⟶ structureModule X) := by
  letI := modulesLinearOverField k f
  let Q := dualSpan α (completeNetSections f α b)
  let eH : (Q ⟶ structureModule X) ≃ₗ[k] cohomologyOverField k f (dualSheaf Q) 0 :=
    MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f Q (structureModule X)
  letI : Subsingleton (cohomologyOverField k f (dualSheaf Q) 0) :=
    MukaiDualSpanDual.completeDualSpanDual_cohomology_zero_subsingleton f α b hgen
  exact ⟨fun a c => eH.injective (Subsingleton.elim _ _)⟩

end M9Native.MukaiDualSpanSections


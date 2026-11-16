module

public import M9StacksIntegration.MukaiPencilQuotient

/-!
# The actual unit morphisms of a complete net span Hom

The original complete cohomology basis is transported by the proved
linear section-to-morphism comparison. This supplies the spanning
condition needed by the genuine extension-kernel construction, without
assuming that an evaluation kernel already equals the Gamma-split space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundle M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiCompleteNetHomBasis

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k))

/-- The complete cohomology basis is a basis of the actual unit Hom
space in the original native scalar structure. -/
def completeNetHomBasis (alpha : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0)) :
    letI := modulesLinearOverField k f
    Module.Basis (ULift.{u} (Fin 3)) k (structureModule X ⟶ alpha) := by
  letI := modulesLinearOverField k f
  exact b.map (MukaiPencilQuotient.sectionHomLinearEquiv f alpha)

/-- This transported basis consists of the original actual sections,
viewed as morphisms from the structure sheaf. -/
theorem completeNetHomBasis_apply (alpha : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0))
    (j : ULift.{u} (Fin 3)) :
    letI := modulesLinearOverField k f
    completeNetHomBasis f alpha b j =
      alpha.unitHomEquiv.symm (completeNetSections f alpha b j) := by
  let := modulesLinearOverField k f
  exact MukaiPencilQuotient.sectionHomLinearEquiv_apply f alpha (b j)

/-- Completeness proves the exact spanning premise of the original
extension-kernel theorem, for the actual complete-net section tuple. -/
theorem completeNetSections_hom_span (alpha : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0)) :
    letI := modulesLinearOverField k f
    letI := (modulesLinearOverField k f).homModule (structureModule X) alpha
    Submodule.span k (Set.range (fun j =>
      (alpha.unitHomEquiv.symm (completeNetSections f alpha b j) :
        structureModule X ⟶ alpha))) = ⊤ := by
  let := modulesLinearOverField k f
  let := (modulesLinearOverField k f).homModule (structureModule X) alpha
  have h : (fun j =>
      (alpha.unitHomEquiv.symm (completeNetSections f alpha b j) :
        structureModule X ⟶ alpha)) = completeNetHomBasis f alpha b := by
    funext j
    exact (completeNetHomBasis_apply f alpha b j).symm
  rw [h]
  exact (completeNetHomBasis f alpha b).span_eq

end M9Native.MukaiCompleteNetHomBasis

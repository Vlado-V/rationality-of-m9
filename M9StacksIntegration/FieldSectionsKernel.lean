module

public import M9StacksIntegration.SheafFieldKernelObstruction
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Sections of an actual kernel on a field spectrum

The genuine affine tilde/sections adjunction makes sections preserve
the actual categorical kernel. The canonical module-category kernel
isomorphism then identifies its actual sections with the usual linear
kernel. This connects the actual Poincare cohomology/kernel comparison
to the actual field-kernel dimension used in the incidence argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.FieldSectionsKernel

/-- The canonical actual sections/linear-kernel equivalence. It uses
the true affine adjunction, without quasi-coherence assumptions. -/
def sectionsKernelEquiv (K : Type u) [Field K]
    {M N : (Spec (.of K)).Modules} (v : M ⟶ N) :
    moduleSpecΓFunctor.obj (kernel v) ≃ₗ[K]
      LinearMap.ker (moduleSpecΓFunctor.map v).hom := by
  let : (moduleSpecΓFunctor (R := .of K)).IsRightAdjoint :=
    (tilde.adjunction (R := .of K)).isRightAdjoint
  exact (PreservesKernel.iso moduleSpecΓFunctor v ≪≫
    ModuleCat.kernelIsoKer (moduleSpecΓFunctor.map v)).toLinearEquiv

theorem finrank_sections_kernel (K : Type u) [Field K]
    {M N : (Spec (.of K)).Modules} (v : M ⟶ N) :
    Module.finrank K (moduleSpecΓFunctor.obj (kernel v)) =
      Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map v).hom) :=
  (sectionsKernelEquiv K v).finrank_eq

/-- An actual module isomorphism to the actual sections of a kernel
gives its actual linear-kernel dimension, with no finiteness premise. -/
theorem finrank_linearKernel_eq_of_iso (K : Type u) [Field K]
    {M N : (Spec (.of K)).Modules} (v : M ⟶ N)
    (V : ModuleCat K) (e : V ≅ moduleSpecΓFunctor.obj (kernel v)) :
    Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map v).hom) =
      Module.finrank K V :=
  (e.toLinearEquiv.finrank_eq.trans (finrank_sections_kernel K v)).symm

end M9Native.FieldSectionsKernel

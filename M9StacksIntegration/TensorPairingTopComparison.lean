module

public import M9StacksIntegration.LinearIncidenceTensorCoordinates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear

/-! The original actual module-sheaf tensor pairing and the native
tensor section are the SAME canonical sheafification-unit pure tensor.
The named native pairing theorem avoids unfolding a product of sheaves. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Opposite
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
universe u

namespace M9Native.TensorPairingTopComparison

theorem pairing_eq_tensorTop (X : Scheme.{u}) (A B : X.Modules)
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
      (Stacks.SheafOfModules.tensorSectionPairing (O := X.sheaf) A B) (op ⊤) s t =
      LinearIncidenceTensorCoordinates.tensorTop X A B s t := by
  refine (Stacks.SheafOfModules.pairingApp_tensorSectionPairing
    (O := X.sheaf) A B (op ⊤) s t).trans ?_
  rfl

end M9Native.TensorPairingTopComparison

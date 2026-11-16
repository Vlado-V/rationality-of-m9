module

public import M9StacksIntegration.PairIncidencePullback

/-! A native pairing summand under the genuine tensor pullback frame.
The base-change equation may retain its original sum dictionary. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.PairIncidencePullbackTerm
open LagrangianMatrixChart LinearIncidenceTensorCoordinates

theorem frame_pairing_apply {A B : Scheme.{u}} (f : A ⟶ B)
    (E L : B.Modules) (E' L' : A.Modules)
    (eE : (Scheme.Modules.pullback f).obj E ≅ E') (eL : (Scheme.Modules.pullback f).obj L ≅ L')
    (s : Γ(E,⊤)) (t : Γ(L,⊤)) :
    (TensorProductPullbackFrame.frame f E L E' L' eE eL).hom.app ⊤
      (pullbackGlobalSections f (tensorObj B E L)
        (Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf B.sheaf)
          (Stacks.SheafOfModules.tensorSectionPairing (O := B.sheaf) E L) (op ⊤) s t)) =
    tensorTop A E' L' (eE.hom.app ⊤ (pullbackGlobalSections f E s))
      (eL.hom.app ⊤ (pullbackGlobalSections f L t)) := by
  exact (congrArg (fun z =>
    (TensorProductPullbackFrame.frame f E L E' L' eE eL).hom.app ⊤
      (pullbackGlobalSections f (tensorObj B E L) z))
    (TensorPairingTopComparison.pairing_eq_tensorTop B E L s t)).trans
      (TensorProductPullbackFrame.frame_apply f E L E' L' eE eL s t)

end M9Native.PairIncidencePullbackTerm

module

public import M9StacksIntegration.HomBundleComparison
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.FiniteLocallyFreeHomSection
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeReflexive

/-!
# Actual tensor presentation of Hom out of the dual

For an actual finite locally free rank-`r` sheaf `Q`, the actual canonical
double-dual morphism and the actual tensor-dual/Hom isomorphism give
`Q tensor F ≅ Hom(Q∨, F)`. This connects the actual curried incidence
section's Hom bundle to the actual tensor bundle whose Chern family
is factored by the flag. No reflexivity or Hom comparison is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.HomDualBundleTensor

/-- The genuine canonical double-dual isomorphism and genuine native
finite locally free tensor/Hom isomorphism, composed at the actual
sheaf objects. The second sheaf is arbitrary. -/
def tensorIsoHomDualBundle {X : Scheme.{u}} (Q F : X.Modules) (r : ℕ)
    [hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj F ≅
      CurriedHomSection.homBundle (dualSheaf Q) F := by
  let : SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q := hQ.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf Q) r :=
    isFiniteLocallyFreeOfRank_dualSheaf Q r hQ
  let e := @asIso _ _ _ _ (toDoubleDual Q)
    (isIso_toDoubleDual_of_isFiniteLocallyFree Q)
  exact ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).mapIso e).app F ≪≫
    Stacks.SheafOfModules.Scheme.dualTensorIsoSheafHomOfRank (dualSheaf Q) F r ≪≫
    (HomBundleComparison.homBundleIsoSheafHom (dualSheaf Q) F).symm

end M9Native.HomDualBundleTensor

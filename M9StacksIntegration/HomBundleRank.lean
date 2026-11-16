module

public import M9StacksIntegration.HomBundleComparison
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.FiniteLocallyFreeHomSection
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree

/-!
# Actual finite locally free rank of the incidence Hom bundle

The actual monoidal Hom bundle that carries the curried incidence
section is isomorphic to the actual tensor product with the dual.
Consequently its rank is the product of the two actual ranks. This
derives the rank-thirty instance from ranks three and ten, rather than
asking for a rank of the incidence bundle as input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.HomBundleRank

/-- The actual tensor-with-dual presentation of the actual Hom bundle. -/
def tensorDualIsoHomBundle {X : Scheme.{u}} (E F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj F).obj (dualSheaf E) ≅
      CurriedHomSection.homBundle E F :=
  Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank E F r ≪≫
    (HomBundleComparison.homBundleIsoSheafHom E F).symm

/-- The actual Hom bundle has rank equal to the product of the two
native ranks. -/
theorem homBundle_rank {X : Scheme.{u}} (E F : X.Modules) (r s : ℕ)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (CurriedHomSection.homBundle E F) (s * r) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf E) r :=
    isFiniteLocallyFreeOfRank_dualSheaf E r hE
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (tensorDualIsoHomBundle E F r)
    (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X F (dualSheaf E) s r)

/-- In particular the actual rank-three-to-rank-ten incidence Hom
bundle has actual rank thirty. -/
theorem homBundle_rank_thirty {X : Scheme.{u}} (E F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 3]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (CurriedHomSection.homBundle E F) 30 :=
  homBundle_rank E F 3 10

end M9Native.HomBundleRank

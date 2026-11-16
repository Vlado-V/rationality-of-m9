module

public import StacksFrontier.AlgebraicGeometry.FlagTower.Tower
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle

/-!
# Properness of the actual native flag tower

This is the small native properness induction from
`FlagTower/ChowPushforward.lean`, lines 55–62, at pinned Stacks commit
`c496df0d9beea9deaeabcea8492605f9a0a2313b`. It uses the actual native
tower, actual tautological kernels, and genuine proper projective-bundle
projections. Keeping this elementary geometric fact in a separate leaf
avoids importing Chow pushforward surjectivity for the section argument.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.FlagTower

universe u

namespace M9Native.FlagTowerProper

instance isProper_tower (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsProper (tower m E).2 := by
  induction m generalizing X with
  | zero => exact inferInstanceAs (IsProper (𝟙 X))
  | succ m ih =>
    have := @ih _ (kernel (bundleTautological E)) (isFiniteLocallyFree_kernel_bundleTautological E)
    exact inferInstanceAs (IsProper ((kernelTower m E).2 ≫ bundleProj E))

end M9Native.FlagTowerProper

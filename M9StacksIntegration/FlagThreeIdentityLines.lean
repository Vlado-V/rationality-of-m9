module

public import M9StacksIntegration.FlagThreeTautological

/-!
# The original identity flag and its three concrete tautological lines

The actual three flag lines are identified with O(1) at the third
projective stage and the actual successive pullbacks of the first two
O(1) lines. Identity and composite pullbacks use the native functor
isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.FlagTower Stacks.Chow

universe u

namespace M9Native.FlagThreeIdentityLines

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} D]

abbrev space1 : Scheme.{u} := bundle D
abbrev kernel1 : (space1 D).Modules := kernel (bundleTautological D)
local instance kernel1Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel1 D) :=
  Stacks.FlagTower.isFiniteLocallyFree_kernel_bundleTautological D
abbrev space2 : Scheme.{u} := bundle (kernel1 D)
abbrev kernel2 : (space2 D).Modules := kernel (bundleTautological (kernel1 D))
local instance kernel2Finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel2 D) :=
  Stacks.FlagTower.isFiniteLocallyFree_kernel_bundleTautological (kernel1 D)
abbrev space3 : Scheme.{u} := bundle (kernel2 D)
abbrev projection2 : space2 D ⟶ space1 D := bundleProj (kernel1 D)
abbrev projection3 : space3 D ⟶ space2 D := bundleProj (kernel2 D)

/-- The actual computed first head of the identity flag. -/
abbrev head1 : FlagThreeQuotient.space D ⟶ space1 D :=
  FlagTowerTautologicalLines.headMap D 2 (FlagThreeQuotient.projection D)
    (FlagThreeTautological.universalPoint D)

/-- The actual computed second head of the identity flag. -/
abbrev head2 : FlagThreeQuotient.space D ⟶ space2 D :=
  FlagTowerTautologicalLines.headMap (kernel1 D) 1
    (FlagTowerTautologicalLines.headMap D 2 (FlagThreeQuotient.projection D)
      (FlagThreeTautological.universalPoint D))
    (FlagTowerTautologicalLines.tailPoint D 2 (FlagThreeQuotient.projection D)
      (FlagThreeTautological.universalPoint D))

/-- The actual computed third head of the identity flag. -/
abbrev head3 : FlagThreeQuotient.space D ⟶ space3 D :=
  FlagTowerTautologicalLines.headMap (kernel2 D) 0
    (head2 D)
    (FlagTowerTautologicalLines.tailPoint (kernel1 D) 1
      (FlagTowerTautologicalLines.headMap D 2 (FlagThreeQuotient.projection D)
        (FlagThreeTautological.universalPoint D))
      (FlagTowerTautologicalLines.tailPoint D 2 (FlagThreeQuotient.projection D)
        (FlagThreeTautological.universalPoint D)))

/-- The original first head is the composition of the third and second
original projective-bundle maps. -/
theorem head1_eq : head1 D = projection3 D ≫ projection2 D := by
  change (𝟙 _ ≫ ((𝟙 _ ≫ projection3 D) ≫ projection2 D)) = _
  simp only [Category.id_comp]

/-- The original second head is the original third projective-bundle map. -/
theorem head2_eq : head2 D = projection3 D := by
  change (𝟙 _ ≫ (𝟙 _ ≫ projection3 D)) = _
  simp only [Category.id_comp]

/-- The original third head is the genuine identity scheme morphism. -/
theorem head3_eq : head3 D = 𝟙 (space3 D) := by
  change (𝟙 (space3 D) ≫ 𝟙 (space3 D)) = _
  exact Category.id_comp _

/-- The last actual flag line is the original third-stage O(1), using
the genuine pullback-by-identity isomorphism. -/
def line3Iso : FlagThreeQuotient.line3 D ≅ bundleTwist (kernel2 D) := by
  let e : FlagThreeQuotient.line3 D ≅
      (Scheme.Modules.pullback (head3 D)).obj (bundleTwist (kernel2 D)) :=
    FlagThreeTautological.line3Iso D
  exact e ≪≫ (Scheme.Modules.pullbackCongr (head3_eq D)).app (bundleTwist (kernel2 D)) ≪≫
    (Scheme.Modules.pullbackId (space3 D)).app (bundleTwist (kernel2 D))

/-- The middle actual flag line is the genuine pullback of the original
second-stage O(1) along the third projective-bundle map. -/
def line2Iso : FlagThreeQuotient.line2 D ≅
    (Scheme.Modules.pullback (projection3 D)).obj (bundleTwist (kernel1 D)) := by
  let e : FlagThreeQuotient.line2 D ≅
      (Scheme.Modules.pullback (head2 D)).obj (bundleTwist (kernel1 D)) :=
    FlagThreeTautological.line2Iso D
  exact e ≪≫ (Scheme.Modules.pullbackCongr (head2_eq D)).app (bundleTwist (kernel1 D))

/-- The first actual flag line is the genuine successive pullback of
O(1) from the first original projective stage. -/
def line1Iso : FlagThreeQuotient.line1 D ≅
    (Scheme.Modules.pullback (projection3 D)).obj
      ((Scheme.Modules.pullback (projection2 D)).obj (bundleTwist D)) := by
  let e : FlagThreeQuotient.line1 D ≅
      (Scheme.Modules.pullback (head1 D)).obj (bundleTwist D) :=
    FlagThreeTautological.line1Iso D
  exact e ≪≫ (Scheme.Modules.pullbackCongr (head1_eq D)).app (bundleTwist D) ≪≫
    ((Scheme.Modules.pullbackComp (projection3 D) (projection2 D)).app (bundleTwist D)).symm

end M9Native.FlagThreeIdentityLines

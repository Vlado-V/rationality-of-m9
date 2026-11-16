module

public import M9StacksIntegration.FlagConsSuccessorLines

/-!
# The actual first three named tower lines are the actual tautological lines

All maps are computed from the original native tower morphism. The
original native tower flag is its literal cons flag, so the normalized
cokernel/kernel comparisons identify its first three named lines with
the actual pullbacks of O(1) on the successive projective bundles.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.FlagTower Stacks.Chow

universe u

namespace M9Native.FlagTowerTautologicalLines

local instance actualHasCokernels {T : Scheme.{u}} : HasCokernels T.Modules := inferInstance
local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasCokernel {T : Scheme.{u}} {A D : T.Modules} (f : A ⟶ D) : HasCokernel f :=
  HasCokernels.has_colimit f
local instance actualHasKernel {T : Scheme.{u}} {A D : T.Modules} (f : A ⟶ D) : HasKernel f :=
  HasKernels.has_limit f

variable {X : Scheme.{u}} (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]

/-- The original first projective-bundle map of the given tower point. -/
abbrev headMap (m : ℕ) {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower (m+1) E).1 // g ≫ (tower (m+1) E).2 = f}) : T ⟶ bundle E :=
  g.1 ≫ (kernelTower m E).2

/-- The genuine map over the first projective bundle into the remaining tower. -/
def tailPoint (m : ℕ) {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower (m+1) E).1 // g ≫ (tower (m+1) E).2 = f}) :
    {g' : T ⟶ (kernelTower m E).1 // g' ≫ (kernelTower m E).2 = headMap E m f g} :=
  ⟨g.1, rfl⟩

/-- The literal actual tail flag used by the native tower constructor. -/
def tailFlag (m : ℕ) {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower (m+1) E).1 // g ≫ (tower (m+1) E).2 = f}) :=
  @towerEquiv m _ (kernel (bundleTautological E))
    (isFiniteLocallyFree_kernel_bundleTautological E) T
    (headMap E m f g) (tailPoint E m f g)

/-- The actual first tautological O(1), pulled back along the actual head map. -/
abbrev line0 (m : ℕ) {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower (m+1) E).1 // g ≫ (tower (m+1) E).2 = f}) : T.Modules :=
  (Scheme.Modules.pullback (headMap E m f g)).obj (bundleTwist E)

/-- The actual second tautological O(1), with no independently supplied map. -/
abbrev line1 (m : ℕ) {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower (m+2) E).1 // g ≫ (tower (m+2) E).2 = f}) : T.Modules :=
  @line0 (bundle E) (kernel (bundleTautological E))
    (isFiniteLocallyFree_kernel_bundleTautological E) m T
    (headMap E (m+1) f g) (tailPoint E (m+1) f g)

/-- The actual third tautological O(1), with both preceding heads computed. -/
abbrev line2 (m : ℕ) {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower (m+3) E).1 // g ≫ (tower (m+3) E).2 = f}) : T.Modules :=
  @line1 (bundle E) (kernel (bundleTautological E))
    (isFiniteLocallyFree_kernel_bundleTautological E) m T
    (headMap E (m+2) f g) (tailPoint E (m+2) f g)

/-- The first original named flag quotient is the actual first O(1). -/
def firstLineIso (m : ℕ) {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower (m+1) E).1 // g ≫ (tower (m+1) E).2 = f}) :
    FlagTowerLines.quotient (towerEquiv (m+1) E f g) 0 ≅ line0 E m f g := by
  let h := (Category.assoc g.1 (kernelTower m E).2 (bundleProj E)).trans g.2
  let j := kernelMapAlong E (headMap E m f g) h
  letI : Mono j := mono_kernelMapAlong E (headMap E m f g) h
  exact FlagConsLines.firstQuotientIso j (rank_cokernel_kernelMapAlong E _ h)
      (tailFlag E m f g) ≪≫
    GenuineChern.cokernelIsoOfShortExact (shortExact_kernelMapAlong E (headMap E m f g) h)

/-- The actual second named line on the literal 2-step native tower. -/
def secondLineIsoTwo {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower 2 E).1 // g ≫ (tower 2 E).2 = f}) :
    FlagTowerLines.kernelLine (towerEquiv 2 E f g)
      (by decide : (0 : Fin 2) ≤ (1 : Fin 2)) ≅ line1 E 0 f g := by
  let h := (Category.assoc g.1 (kernelTower 1 E).2 (bundleProj E)).trans g.2
  let j := kernelMapAlong E (headMap E 1 f g) h
  letI : Mono j := mono_kernelMapAlong E (headMap E 1 f g) h
  have hF : towerEquiv 2 E f g =
      Flag.cons j (rank_cokernel_kernelMapAlong E _ h) (tailFlag E 1 f g) :=
    towerEquiv_succ_apply 1 E f g
  let e0 := eqToIso (congrArg (fun F : Flag ((Scheme.Modules.pullback f).obj E) 2 =>
    FlagTowerLines.kernelLine F (by decide : (0 : Fin 2) ≤ (1 : Fin 2))) hF)
  let e1 := FlagConsLines.firstKernelLineIso j (rank_cokernel_kernelMapAlong E _ h)
    (tailFlag E 1 f g) (0 : Fin 1)
  let e2 := @firstLineIso (bundle E) (kernel (bundleTautological E))
    (isFiniteLocallyFree_kernel_bundleTautological E) 0 T
    (headMap E 1 f g) (tailPoint E 1 f g)
  exact e0 ≪≫ e1 ≪≫ e2

/-- The actual second original line is the original first tail quotient. -/
def secondKernelTailIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower 3 E).1 // g ≫ (tower 3 E).2 = f}) :
    FlagTowerLines.kernelLine (towerEquiv 3 E f g)
      (by decide : (0 : Fin 3) ≤ (1 : Fin 3)) ≅
        FlagTowerLines.quotient (tailFlag E 2 f g) 0 := by
  let h := (Category.assoc g.1 (kernelTower 2 E).2 (bundleProj E)).trans g.2
  let j := kernelMapAlong E (headMap E 2 f g) h
  letI : Mono j := mono_kernelMapAlong E (headMap E 2 f g) h
  have hF : towerEquiv 3 E f g =
      Flag.cons j (rank_cokernel_kernelMapAlong E _ h) (tailFlag E 2 f g) :=
    towerEquiv_succ_apply 2 E f g
  let e0 := eqToIso (congrArg (fun F : Flag ((Scheme.Modules.pullback f).obj E) 3 =>
    FlagTowerLines.kernelLine F (by decide : (0 : Fin 3) ≤ (1 : Fin 3))) hF)
  let e1 := FlagConsLines.firstKernelLineIso j (rank_cokernel_kernelMapAlong E _ h)
    (tailFlag E 2 f g) (0 : Fin 2)
  exact e0 ≪≫ e1

/-- The actual first quotient of the actual tail is the second O(1). -/
def tailFirstLineIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower 3 E).1 // g ≫ (tower 3 E).2 = f}) :
    FlagTowerLines.quotient (tailFlag E 2 f g) 0 ≅ line1 E 1 f g := by
  let F : (bundle E).Modules := kernel (bundleTautological E)
  letI hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    isFiniteLocallyFree_kernel_bundleTautological E
  let e := @firstLineIso (bundle E) F hF 1 T
    (headMap E 2 f g) (tailPoint E 2 f g)
  exact e

/-- The actual second named line on the original three-step native tower. -/
def secondLineIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower 3 E).1 // g ≫ (tower 3 E).2 = f}) :
    FlagTowerLines.kernelLine (towerEquiv 3 E f g)
      (by decide : (0 : Fin 3) ≤ (1 : Fin 3)) ≅ line1 E 1 f g :=
  secondKernelTailIso E f g ≪≫ tailFirstLineIso E f g

/-- The actual third original line is the original second tail line. -/
def thirdKernelTailIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower 3 E).1 // g ≫ (tower 3 E).2 = f}) :
    FlagTowerLines.kernelLine (towerEquiv 3 E f g)
      (by decide : (1 : Fin 3) ≤ (2 : Fin 3)) ≅
        FlagTowerLines.kernelLine (tailFlag E 2 f g)
          (by decide : (0 : Fin 2) ≤ (1 : Fin 2)) := by
  let h := (Category.assoc g.1 (kernelTower 2 E).2 (bundleProj E)).trans g.2
  let j := kernelMapAlong E (headMap E 2 f g) h
  letI : Mono j := mono_kernelMapAlong E (headMap E 2 f g) h
  have hF : towerEquiv 3 E f g =
      Flag.cons j (rank_cokernel_kernelMapAlong E _ h) (tailFlag E 2 f g) :=
    towerEquiv_succ_apply 2 E f g
  let e0 := eqToIso (congrArg (fun F : Flag ((Scheme.Modules.pullback f).obj E) 3 =>
    FlagTowerLines.kernelLine F (by decide : (1 : Fin 3) ≤ (2 : Fin 3))) hF)
  let e1 := FlagConsSuccessorLines.successorKernelLineIso j (rank_cokernel_kernelMapAlong E _ h)
    (tailFlag E 2 f g) (by decide : (0 : Fin 2) ≤ (1 : Fin 2))
  exact e0 ≪≫ e1

/-- The actual second tail line is the third original tautological O(1). -/
def tailSecondLineIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower 3 E).1 // g ≫ (tower 3 E).2 = f}) :
    FlagTowerLines.kernelLine (tailFlag E 2 f g)
      (by decide : (0 : Fin 2) ≤ (1 : Fin 2)) ≅ line2 E 0 f g :=
  @secondLineIsoTwo (bundle E) (kernel (bundleTautological E))
    (isFiniteLocallyFree_kernel_bundleTautological E) T
    (headMap E 2 f g) (tailPoint E 2 f g)

/-- The actual third named line on the original three-step native tower. -/
def thirdLineIso {T : Scheme.{u}} (f : T ⟶ X)
    (g : {g : T ⟶ (tower 3 E).1 // g ≫ (tower 3 E).2 = f}) :
    FlagTowerLines.kernelLine (towerEquiv 3 E f g)
      (by decide : (1 : Fin 3) ≤ (2 : Fin 3)) ≅ line2 E 0 f g :=
  thirdKernelTailIso E f g ≪≫ tailSecondLineIso E f g

end M9Native.FlagTowerTautologicalLines

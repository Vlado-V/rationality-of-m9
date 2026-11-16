module

public import M9StacksIntegration.LagrangianPolynomialProperPush
public import M9StacksIntegration.LagrangianFlagFundamentalTransport
public import M9StacksIntegration.LagrangianFlagLineTransport
public import M9StacksIntegration.LagrangianFlagChernNumerator
public import M9StacksIntegration.LagrangianPolynomialLineCongruence

/-!
# Polynomial caps under the original Grassmannian/flag isomorphism

All three original positive quotient lines are preserved by the native
flag isomorphism. Genuine proper-cap compatibility therefore transports
every polynomial operator on every original Chow class. Applying the
proved fundamental-class transport gives the original degree-twelve
identity with no compatibility or fundamental identity as an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow Stacks.FlagTower
universe u
namespace M9Native.LagrangianFlagPolynomialTransport
open ChowCapWords LagrangianChowPolynomials LagrangianFlagFundamentalTransport

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) :
    HasKernel f := HasKernels.has_limit f

variable (K : Type u) [Field K]

local instance quotientFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
    (LagrangianGrassmannian.quotientBundle K) :=
  (LagrangianGrassmannian.quotientBundle_rank K).isFiniteLocallyFree

local instance freeSixFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
    (Stacks.FlagTower.freeModule 6 (Spec (.of K))) :=
  Stacks.FlagTower.isFiniteLocallyFree_freeModule 6 (Spec (.of K))

local instance freeSixRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (Stacks.FlagTower.freeModule 6 (Spec (.of K))) 6 :=
  Stacks.FlagTower.rank_freeModule 6 (Spec (.of K))

/-- The three ORIGINAL named quotient lines on the flag of the actual universal quotient. -/
def linesA : Fin 3 → InvertibleLine (spaceA K) :=
  ![LagrangianFlagChernNumerator.firstLine (LagrangianGrassmannian.quotientBundle K),
    LagrangianFlagChernNumerator.secondLine (LagrangianGrassmannian.quotientBundle K),
    LagrangianFlagChernNumerator.thirdLine (LagrangianGrassmannian.quotientBundle K)]

/-- The three ORIGINAL named quotient lines on the native free-six flag. -/
def linesB : Fin 3 → InvertibleLine (spaceB K) :=
  ![LagrangianFlagChernNumerator.firstLine (Stacks.FlagTower.freeModule 6 (Spec (.of K))),
    LagrangianFlagChernNumerator.secondLine (Stacks.FlagTower.freeModule 6 (Spec (.of K))),
    LagrangianFlagChernNumerator.thirdLine (Stacks.FlagTower.freeModule 6 (Spec (.of K)))]

/-- The actual native first/middle/last line comparisons, in the proper-push direction. -/
def lineIso (i : Fin 3) :
    (linesA K i).1 ≅ (Scheme.Modules.pullback (towerIso K).hom).obj (linesB K i).1 := by
  exact Fin.cases (LagrangianFlagLineTransport.firstLineIso K).symm
    (fun j => Fin.cases (LagrangianFlagLineTransport.secondLineIso K).symm
      (fun l => Fin.cases (LagrangianFlagLineTransport.thirdLineIso K).symm
        (fun t => Fin.elim0 t) l) j) i

/-- Compatibility holds for every genuine cap degree and original Chow input. -/
theorem isoChowPush_evaluate_apply (P : MvPolynomial (Fin 3) ℤ)
    (k : ℤ) (i : ℕ) (α : chowGroup (fieldChowSituation K) (qA K) k) :
    isoChowPush K (k-(i:ℤ)) (evaluate (fieldChowSituation K) (qA K) (linesA K) P k i α) =
      evaluate (fieldChowSituation K) (qB K) (linesB K) P k i (isoChowPush K k α) :=
  LagrangianPolynomialProperPush.properPush_evaluate_apply (fieldChowSituation K)
    (qA K) (qB K) (towerIso K).hom (towerIso_hom_comp K)
    (linesB K) (linesA K) (lineIso K) P k i α

/-- The actual polynomial cap of the ORIGINAL fundamental class is preserved. -/
theorem isoChowPush_evaluate_fundamental (P : MvPolynomial (Fin 3) ℤ) :
    isoChowPush K 0
      (evaluate (fieldChowSituation K) (qA K) (linesA K) P 12 12 (fundamentalA K)) =
      evaluate (fieldChowSituation K) (qB K) (linesB K) P 12 12 (fundamentalB K) := by
  have h := isoChowPush_evaluate_apply K P 12 12 (fundamentalA K)
  rw [isoChowPush_fundamentalA] at h
  exact h

/-- The same identity for the two actual iterated flat-pullback constructions. -/
theorem isoChowPush_evaluate_iteratedPull (P : MvPolynomial (Fin 3) ℤ) :
    isoChowPush K 0
      (evaluate (fieldChowSituation K) (qA K) (linesA K) P 12 12 (iteratedPullA K)) =
      evaluate (fieldChowSituation K) (qB K) (linesB K) P 12 12 (iteratedPullB K) := by
  rw [iteratedPullA_eq_fundamentalA, iteratedPullB_eq_fundamentalB]
  exact isoChowPush_evaluate_fundamental K P

/-- The free-flag roots are literally those in the actual integral-sixteen theorem. -/
theorem linesB_eq_original :
    linesB K = LagrangianPolynomialLineCongruence.originalLines
      (Stacks.FlagTower.freeModule 6 (Spec (.of K))) := by
  funext i
  apply Subtype.ext
  fin_cases i <;> rfl

end M9Native.LagrangianFlagPolynomialTransport

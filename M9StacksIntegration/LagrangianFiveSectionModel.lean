module

public import M9StacksIntegration.LagrangianFiveEquationDeterminant
public import M9StacksIntegration.LagrangianSmoothSectionConormal
public import M9StacksIntegration.LagrangianPluckerQuotient
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological

/-!
# The actual original five-section model and conormal determinant

The equation sheaf is literally the original determinant line tensor
the original free-five sheaf. Its section defines the actual native zero
scheme. Smooth relative dimension one supplies the genuine conormal
sequence, and the actual dual-equation determinant has exponent minus five.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant
open M9Native.LagrangianGrassmannian
open M9Native.LagrangianMatrixChart
open M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianConormalDeterminantPullback

universe u

namespace M9Native.LagrangianFiveSectionModel

variable (K : Type u) [Field K]

/-- The literal line-first bundle of five equations on the original LG. -/
abbrev equationBundle : (space K).Modules :=
  tensor (determinantLine K) (freeOn (space K) 5)

/-- The line is invertible because the original quotient has rank three. -/
theorem determinantLine_isInvertible :
    SheafOfModules.IsInvertible (space K).presheaf (space K).ringCatSheaf.2
      (determinantLine K) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (determinantLine_invertible K)

/-- Rank five is proved from the original line and the literal free-five sheaf. -/
@[instance] theorem equationBundle_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (equationBundle K) 5 := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn (space K) 5) 5 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv
      (ULift.{u} (Fin 5)) 5 Equiv.ulift
  exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (space K)
    (determinantLine K) (freeOn (space K) 5) 1 5

@[instance] theorem equationBundle_finiteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (equationBundle K) :=
  (equationBundle_rank K).isFiniteLocallyFree

variable (s : Γ(equationBundle K, ⊤))

/-- The actual native zero scheme of the actual five equations. -/
abbrev curve : Scheme.{u} := SectionZeroConormal.space (equationBundle K) s

/-- The original native closed immersion, before any smoothness hypothesis. -/
abbrev inclusion : curve K s ⟶ space K :=
  SectionZeroConormal.inclusion (equationBundle K) s

/-- The original structural morphism of the actual zero scheme. -/
abbrev structureMap : curve K s ⟶ Spec (.of K) := inclusion K s ≫ projection K

/-- The literal original pulled determinant line. -/
abbrev curveLine : (curve K s).Modules :=
  (Scheme.Modules.pullback (inclusion K s)).obj (determinantLine K)

/-- Invertibility of the actual pulled line is a consequence, not an input. -/
theorem curveLine_isInvertible :
    SheafOfModules.IsInvertible (curve K s).presheaf (curve K s).ringCatSheaf.2
      (curveLine K s) := by
  letI := determinantLine_isInvertible K
  exact pulledLine_isInvertible (inclusion K s) (determinantLine K)

variable [SmoothOfRelativeDimension 1 (structureMap K s)]

/-- The actual native conormal complex, with literal original equation-dual source. -/
abbrev conormalSequence :=
  LagrangianSmoothSectionConormal.equationSequence K (equationBundle K) s

/-- Smooth curve geometry proves short exactness of the actual conormal maps. -/
theorem conormalSequence_shortExact : (conormalSequence K s).ShortExact :=
  LagrangianSmoothSectionConormal.equationSequence_shortExact K (equationBundle K) s

/-- The actual first term has rank five by original duality and pullback. -/
theorem conormalSource_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalSequence K s).X₁ 5 := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (dualSheaf (equationBundle K)) 5 :=
    isFiniteLocallyFreeOfRank_dualSheaf (equationBundle K) 5 (equationBundle_rank K)
  exact isFiniteLocallyFreeOfRank_pullback (inclusion K s) (dualSheaf (equationBundle K)) 5

/-- Smooth relative dimension one proves the actual quotient has rank one. -/
theorem curveDifferentials_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (conormalSequence K s).X₃ 1 :=
  LagrangianCurveConormal.quotient_rank K (inclusion K s)

/-- The determinant of the actual original first term has exponent minus five,
with all line invertibility and equation-dual comparisons derived internally. -/
def conormalSourceDeterminantIso :
    letI := curveLine_isInvertible K s
    topExterior (conormalSequence K s).X₁ 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower (curve K s).presheaf
        (curve K s).ringCatSheaf.2 (curveLine K s) (-5) := by
  letI := determinantLine_isInvertible K
  letI := curveLine_isInvertible K s
  exact LagrangianFiveEquationDeterminant.pulledFiveEquationDualTopIso
    (inclusion K s) (determinantLine K)

end M9Native.LagrangianFiveSectionModel

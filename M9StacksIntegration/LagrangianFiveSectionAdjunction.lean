module

public import M9StacksIntegration.LagrangianCanonicalDeterminant
public import M9StacksIntegration.LagrangianFiveSectionModel

/-!
# Actual differentials of a smooth five-section curve in the original LG

The original equation bundle is literally the original determinant line
tensor the original free-five sheaf, in that order. For the actual zero
scheme of an actual section, smooth relative dimension one derives the
genuine conormal short exact sequence. Its two determinant calculations
give the actual differential line, with no determinant, conormal-rank,
normal-map or line-comparison premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundleDeterminant
open M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianConormalDeterminantPullback
open M9Native.LagrangianFiveSectionModel

universe u

namespace M9Native.LagrangianFiveSectionAdjunction

variable (K : Type u) [Field K] [CharZero K]
  (s : Γ(equationBundle K, ⊤)) [SmoothOfRelativeDimension 1 (structureMap K s)]

/-- Actual smoothness and the actual five equations yield the actual
native differential-line isomorphism. The determinant identifications,
conormal rank and defining section model are all derived internally. -/
def differentialsIsoCurveLine :
    Scheme.Hom.relativeDifferentials (structureMap K s) ≅ curveLine K s := by
  letI := LagrangianCanonicalDeterminant.determinantLine_isInvertible K
  letI := curveLine_isInvertible K s
  letI := conormalSource_rank K s
  letI := curveDifferentials_rank K s
  exact LagrangianCurveAdjunction.fiveSectionAdjunction
    (conormalSequence K s) (conormalSequence_shortExact K s) (curveLine K s)
    (conormalSourceDeterminantIso K s)
    (topExteriorPullbackOfIntegerIso (inclusion K s)
      (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K)) 6
      (determinantLine K) (-4)
      (LagrangianCanonicalDeterminant.cotangentDeterminantIso K))

end M9Native.LagrangianFiveSectionAdjunction

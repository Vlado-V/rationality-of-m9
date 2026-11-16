module

public import M9StacksIntegration.CurvePowerGraphMapRestrictions
public import M9StacksIntegration.GraphNormalPicard
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf

/-!
# The actual graph divisors on native curve powers

The original point graph is the original genuine degree-one family of
the checked graph provider. Its actual kernel ideal is Cartier. The
same provider identifies its actual self-restriction with the pulled
back cotangent line, over the literal native curve power.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphCartier

variable {S : Scheme.{u}} (C : Over S) [IsSeparated C.hom]
  [SmoothOfRelativeDimension 1 C.hom]

abbrev graphSection (m : ℕ) (y : power C m ⟶ C) :
    (power C m).left ⟶ (power C (m + 1)).left :=
  Stacks.Hilbert.pointGraph C (power C m) y

omit [IsSeparated C.hom] [SmoothOfRelativeDimension 1 C.hom] in
theorem graphSection_comp_second (m : ℕ) (y : power C m ⟶ C) :
    graphSection C m y ≫ (snd C (power C m)).left = 𝟙 _ :=
  Stacks.Hilbert.pointGraph_comp_snd C (power C m) y

theorem graphIdeal_isEffectiveCartier (m : ℕ) (y : power C m ⟶ C) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Hilbert.pointIdeal C (power C m) y) :=
  (GraphNormalPicard.graphFamily C (power C m) y).isEffectiveCartierDivisor_ideal

abbrev graphClass (m : ℕ) (y : power C m ⟶ C) :
    Stacks.Picard.ofScheme (power C (m + 1)).left :=
  (GraphNormalPicard.graphFamily C (power C m) y).picardClass

abbrev graphLine (m : ℕ) (y : power C m ⟶ C) : (power C (m + 1)).left.Modules :=
  Stacks.Divisors.invertibleSheaf (Stacks.Hilbert.pointIdeal C (power C m) y)

theorem graphLine_isInvertible (m : ℕ) (y : power C m ⟶ C) :
    SheafOfModules.IsInvertible (power C (m + 1)).left.presheaf
      (power C (m + 1)).left.ringCatSheaf.property (graphLine C m y) := by
  exact @Stacks.Divisors.isInvertible_invertibleSheaf _
    (Stacks.Hilbert.pointIdeal C (power C m) y) (graphIdeal_isEffectiveCartier C m y)

theorem graph_self_class (m : ℕ) (y : power C m ⟶ C) :
    Stacks.Picard.schemePullbackClass (graphSection C m y) (graphClass C m y) =
      -Stacks.Picard.schemePullbackClass y.left
        (Stacks.SheafOfModules.picardClass C.left.presheaf C.left.ringCatIsSheaf
          (Scheme.Hom.relativeDifferentials C.hom)
          (DiagonalNormalPicard.differentials_isInvertible C.hom)) :=
  GraphNormalPicard.graph_self_picardClass C (power C m) y

end M9Native.CurvePowerGraphCartier

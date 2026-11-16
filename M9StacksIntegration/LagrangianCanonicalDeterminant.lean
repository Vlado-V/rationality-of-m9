module

public import M9StacksIntegration.LagrangianGlobalCotangent
public import M9StacksIntegration.SymmetricSquareDualDeterminant

/-!
# The actual cotangent determinant of the original Lagrangian Grassmannian

The global intrinsic cotangent isomorphism, the genuine symmetric-square
determinant, and native exterior-dual/integer-power normalization give
the minus-fourth power of the original universal quotient determinant.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundleDeterminant
open M9Native.LagrangianGrassmannian
open M9Native.LagrangianPluckerQuotient

universe u

namespace M9Native.LagrangianCanonicalDeterminant

variable (K : Type u) [Field K]

/-- Invertibility is derived from the actual rank-three universal quotient. -/
theorem determinantLine_isInvertible :
    SheafOfModules.IsInvertible (space K).presheaf (space K).ringCatSheaf.2
      (determinantLine K) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (determinantLine_invertible K)

variable [CharZero K]

/-- The actual structural coefficient map carries the inverse of two
to an inverse of two in the original global section ring. -/
@[instance_reducible] def twoInvertible : Invertible (2 : Γ(space K, ⊤)) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  exact (Invertible.map (LagrangianPlucker.coefficientMap K (𝟙 (space K))) (2 : K)).copy
    (2 : Γ(space K, ⊤)) (by
      calc
        (2 : Γ(space K, ⊤)) = 1 + 1 := one_add_one_eq_two.symm
        _ = (LagrangianPlucker.coefficientMap K (𝟙 (space K))) (1 + 1) := by
          rw [map_add, map_one]
        _ = (LagrangianPlucker.coefficientMap K (𝟙 (space K))) (2 : K) :=
          congrArg _ one_add_one_eq_two)

/-- The literal native cotangent determinant of LG is the native integer
power minus four of the literal universal quotient determinant line.
There is no cotangent or determinant comparison premise. -/
def cotangentDeterminantIso :
    letI := determinantLine_isInvertible K
    topExterior (Scheme.Hom.relativeDifferentials (projection K)) 6 ≅
      Stacks.SheafOfModules.Invertible.tensorPower (space K).presheaf
        (space K).ringCatSheaf.2 (determinantLine K) (-4) := by
  letI := determinantLine_isInvertible K
  letI := twoInvertible K
  exact (Scheme.Modules.exteriorPowerFunctor (space K) (6 : ℤ)).mapIso
      (LagrangianGlobalCotangent.cotangentIso K) ≪≫
    SymmetricSquareDualDeterminant.symmetricSquareDualDeterminantIso
      (quotientOnLG K).target

end M9Native.LagrangianCanonicalDeterminant

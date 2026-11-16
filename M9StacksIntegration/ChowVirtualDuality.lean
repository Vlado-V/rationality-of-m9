module

public import M9StacksIntegration.GradedCapVirtualSchur
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernClassDual

/-!
# The genuine dual-sign comparison for the actual virtual Chow family

The pinned unconditional native dual-Chern theorem identifies the total
Chern cap family of the actual dual bundle with the signed family of the
original bundle. Inverting these actual units proves that the signed
inverse family of E-dual is exactly the inverse family of E.

This is the comparison needed on tower3(E-dual): the incidence bundle is
Hom(Q3-dual, pullback F), hence Q3 tensor pullback F, with positive
quotient roots. Its signed inverse-dual coefficients therefore retain
the actual virtual order c(F)c(E)^{-1}. Neither a dual-sign identity nor
a Schur, trace, splitting, or Chow-realization premise is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u v

namespace M9Native.ChowVirtualDuality

open GradedCapVirtualSchur

/-- Twice changing the sign of every odd component is the identity
on the native operator ring; no commutativity is used. -/
theorem signScale_involutive {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]
    (a : GradedCapFamily G) :
    capFamilySignScale (capFamilySignScale a) = a := by
  funext k i
  refine AddMonoidHom.ext fun α => ?_
  rw [capFamilySignScale_apply, capFamilySignScale_apply, smul_smul,
    ← mul_pow, show (-1 : ℤ)*(-1) = 1 by decide, one_pow, one_smul]

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q] (E : X.Modules) (r : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]

local instance dualRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf E) r :=
  isFiniteLocallyFreeOfRank_dualSheaf E r hE

/-- This is the unconditional pinned native theorem on the literal
actual dual bundle and the actual integral Chow cap families. -/
theorem actual_dualFamily :
    chernFamily C q (dualSheaf E) r = capFamilySignScale (chernFamily C q E r) :=
  chernFamily_dualSheaf C r q E

/-- The signed inverse-dual family equals the actual inverse original
family, by native duality and two-sided inverse uniqueness. -/
theorem signed_inverse_dualFamily :
    capFamilySignScale (inverseFamily C q (dualSheaf E) r) =
      inverseFamily C q E r := by
  have hdual : capFamilySignScale (chernFamily C q (dualSheaf E) r) =
      chernFamily C q E r := by
    rw [actual_dualFamily, signScale_involutive]
  have hright : chernFamily C q E r *
      capFamilySignScale (inverseFamily C q (dualSheaf E) r) = 1 := by
    rw [← hdual, ← capFamilySignScale_mul]
    simp only [inverseFamily, IsUnit.mul_val_inv, capFamilySignScale_one]
  have hleft : inverseFamily C q E r * chernFamily C q E r = 1 := by
    simp only [inverseFamily, IsUnit.val_inv_mul]
  calc
    capFamilySignScale (inverseFamily C q (dualSheaf E) r) =
        (inverseFamily C q E r * chernFamily C q E r) *
          capFamilySignScale (inverseFamily C q (dualSheaf E) r) := by
      rw [hleft, one_mul]
    _ = inverseFamily C q E r *
        (chernFamily C q E r * capFamilySignScale (inverseFamily C q (dualSheaf E) r)) :=
      mul_assoc _ _ _
    _ = inverseFamily C q E r := by rw [hright, mul_one]

/-- The comparison in each actual Chow degree, including coefficients
above the ranks of the original bundles. -/
theorem signed_inverse_dual_apply (k : ℤ) (i : ℕ) (α : chowGroup C q k) :
    (-1 : ℤ)^i • inverseFamily C q (dualSheaf E) r k i α =
      inverseFamily C q E r k i α :=
  congrArg (fun a : GradedCapFamily (chowGroup C q) => a k i α)
    (signed_inverse_dualFamily C q E r)

/-- The inverse actual dual family is the signed actual original
inverse family. This uses the proved involution, not a second premise. -/
theorem inverse_dualFamily :
    inverseFamily C q (dualSheaf E) r = capFamilySignScale (inverseFamily C q E r) := by
  have h := congrArg capFamilySignScale (signed_inverse_dualFamily C q E r)
  rwa [signScale_involutive] at h

/-- The actual incidence convention gives precisely the original
virtual family, with c(F) on the left and the signed inverse-dual
coefficient family on the right. -/
theorem virtualFamily_eq_signed_inverse_dual
    (F : X.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F s] :
    virtualFamily C q F E s r =
      chernFamily C q F s * capFamilySignScale (inverseFamily C q (dualSheaf E) r) := by
  rw [signed_inverse_dualFamily]
  rfl

end M9Native.ChowVirtualDuality

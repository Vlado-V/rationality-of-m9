module

public import M9StacksIntegration.ChowSignedVirtualFamily
public import M9StacksIntegration.ChowChernLineCommutation

/-!
# Genuine signed-source Chern families commute with the same original line cap

The sign operator sends a degree-one line family to its negative. Native
multiplicativity therefore transports actual inverse/line commutation to
the signed inverse, without an ambient commutative operational ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
universe u v
namespace M9Native.ChowSignedVirtualLineCommutation
open GradedCapVirtualSchur ChowCapWords GradedLineCapSubring

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- Degree-sign scaling of an actual homogeneous degree-one cap is negation. -/
theorem signScale_of_homogeneous_one (x : GradedCapFamily G) (hx : x.IsHomogeneous 1) :
    capFamilySignScale x = -x := by
  funext k i
  apply AddMonoidHom.ext
  intro α
  by_cases hi : i=1
  · subst i
    change ((-1:ℤ)^1) • (x k 1 α) = -(x k 1 α)
    simp only [pow_one, neg_one_zsmul]
  · simp only [capFamilySignScale_apply, hx k i hi, AddMonoidHom.zero_apply,
      smul_zero, Pi.neg_apply, AddMonoidHom.neg_apply, neg_zero]

/-- Multiplicative native sign scaling preserves commutation with an
original degree-one family, after cancelling only its additive negative. -/
theorem commute_signScale_of_homogeneous_one (a x : GradedCapFamily G)
    (hx : x.IsHomogeneous 1) (h : Commute a x) :
    Commute (capFamilySignScale a) x := by
  have hs := congrArg capFamilySignScale h.eq
  simp only [capFamilySignScale_mul, signScale_of_homogeneous_one x hx] at hs
  rw [mul_neg, neg_mul] at hs
  exact neg_injective hs

end Generic

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]
    (D : X.Modules) (rD : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D rD]
    (L : InvertibleLine X)

/-- Actual inverse/line commutation gives the same original line for
the actual signed source inverse. -/
theorem signedInverse_commute_lineFamily :
    Commute (capFamilySignScale (inverseFamily C q D rD)) (lineFamily C q L) :=
  commute_signScale_of_homogeneous_one _ _ (lineFamily_homogeneous C q L)
    (ChowChernLineCommutation.inverseFamily_commute_lineFamily C q D rD L)

/-- The actual signed-source family commutes with the SAME original
line cap, using genuine native Chern and inverse commutation. -/
theorem signedVirtual_commute_lineFamily (F : X.Modules) (rF : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF] :
    Commute (ChowSignedVirtualFamily.family C q F D rF rD) (lineFamily C q L) := by
  have hF := ChowChernLineCommutation.chernFamily_commute_lineFamily C q F rF L
  have hD := signedInverse_commute_lineFamily C q D rD L
  change (chernFamily C q F rF * capFamilySignScale (inverseFamily C q D rD)) *
    lineFamily C q L = lineFamily C q L *
      (chernFamily C q F rF * capFamilySignScale (inverseFamily C q D rD))
  rw [mul_assoc, hD.eq, ← mul_assoc, hF.eq, mul_assoc]

/-- Every finite homogeneous coefficient has proved commutation with
the original degree-one line, without a global operational CommRing. -/
theorem lineFamily_commute_homComponent (F : X.Modules) (rF : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F rF] (i : ℕ) :
    Commute (lineFamily C q L)
      (homComponent i (ChowSignedVirtualFamily.family C q F D rF rD)) :=
  commute_homComponent (lineFamily_homogeneous C q L)
    (signedVirtual_commute_lineFamily C q D rD L F rF).symm i

end M9Native.ChowSignedVirtualLineCommutation

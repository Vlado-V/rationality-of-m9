module

public import M9StacksIntegration.ChowVirtualDuality
public import M9StacksIntegration.ChowFreeBundleChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedPowerSum

/-!
# The integral degree-two Chern relation of an actual symplectic quotient

For a genuine short exact sequence Q-dual -> F -> Q with F actually
isomorphic to a free bundle, native Whitney, native duality and native
free-bundle normalization give c1(Q)^2 = 2 c2(Q).  This is an equality
of the original ordered integral Chow cap operators.  No inverse of 2,
Chow torsion hypothesis or splitting-principle premise is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern Stacks.AlgebraicGeometry.ReflexiveModules

universe u v

namespace M9Native.SymplecticQuotientChernRelation

section Operators
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- Selecting a component retains the actual integral duality sign. -/
theorem homComponent_signScale (a : GradedCapFamily G) (i : ℕ) :
    homComponent i (capFamilySignScale a) = (-1 : ℤ)^i • homComponent i a := by
  classical
  funext k j
  apply AddMonoidHom.ext
  intro x
  by_cases hji : j = i
  · subst j
    simp [homComponent_apply_self, capFamilySignScale_apply]
  · simp [homComponent_apply_of_ne hji]

/-- The second coefficient of c(-t)c(t)=1 gives the integral relation,
in the actual generally noncommutative cap ring. -/
theorem first_square_eq_two_second (a : GradedCapFamily G)
    (hzero : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (hinverse : capFamilySignScale a * a = 1) :
    homComponent 1 a * homComponent 1 a = (2 : ℤ) • homComponent 2 a := by
  have h0 : homComponent 0 a = 1 := homComponent_zero_of_apply_zero hzero
  have h2one : homComponent 2 (1 : GradedCapFamily G) = 0 :=
    GradedCapFamily.IsHomogeneous.one.homComponent_of_ne (by decide)
  have h := congrArg (homComponent 2) hinverse
  rw [homComponent_mul] at h
  have heq : homComponent 2 a - homComponent 1 a * homComponent 1 a +
      homComponent 2 a = 0 := by
    simpa [Finset.sum_range_succ, homComponent_signScale, h0, h2one,
      neg_mul, sub_eq_add_neg] using h
  rw [two_zsmul]
  symm
  apply sub_eq_zero.mp
  calc
    homComponent 2 a + homComponent 2 a - homComponent 1 a * homComponent 1 a =
        homComponent 2 a - homComponent 1 a * homComponent 1 a + homComponent 2 a := by abel
    _ = 0 := heq

/-- Four further actual first-Chern caps give the same integral factor 2. -/
theorem first_sixth_eq_two_second_first_fourth (a : GradedCapFamily G)
    (hzero : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (hinverse : capFamilySignScale a * a = 1) :
    homComponent 1 a ^ 6 =
      (2 : ℤ) • (homComponent 2 a * homComponent 1 a ^ 4) := by
  calc
    homComponent 1 a ^ 6 =
        (homComponent 1 a * homComponent 1 a) * homComponent 1 a ^ 4 := by
      rw [← pow_two, ← pow_add]
    _ = ((2 : ℤ) • homComponent 2 a) * homComponent 1 a ^ 4 := by
      rw [first_square_eq_two_second a hzero hinverse]
    _ = _ := by simp only [two_zsmul, add_mul]

end Operators

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q] (Q : X.Modules) (r : ℕ)
  [hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q r]

local instance dualRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf Q) r :=
  isFiniteLocallyFreeOfRank_dualSheaf Q r hQ

variable (F : X.Modules) (i : dualSheaf Q ⟶ F) (p : F ⟶ Q)
  (w : i ≫ p = 0) (hseq : (ShortComplex.mk i p w).ShortExact)
  (e : F ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r+r))))

include hseq e in
/-- Actual Whitney and the actual free middle term give the true inverse relation. -/
theorem signed_chern_mul_eq_one :
    capFamilySignScale (chernFamily C q Q r) * chernFamily C q Q r = 1 := by
  let _ := isFiniteLocallyFreeOfRank_of_shortExact (ShortComplex.mk i p w) hseq r r
    (dualRank Q r) hQ
  have hw := chernFamily_eq_mul_of_shortExact C q (ShortComplex.mk i p w) hseq r r
  have hf := ChowFreeBundleChern.chernFamily_eq_one_of_iso_free C q F (r+r) e
  rw [ChowVirtualDuality.actual_dualFamily C q Q r] at hw
  exact hw.symm.trans hf

include hseq e in
/-- The actual c1/c2 identity on all original integral Chow groups. -/
theorem chern_first_square_eq_two_second :
    homComponent 1 (chernFamily C q Q r) * homComponent 1 (chernFamily C q Q r) =
      (2 : ℤ) • homComponent 2 (chernFamily C q Q r) :=
  first_square_eq_two_second _ (chernFamily_apply_zero C q Q r)
    (signed_chern_mul_eq_one C q Q r F i p w hseq e)

include hseq e in
/-- The actual sixfold cap relation before applying any degree homomorphism. -/
theorem chern_first_sixth_eq_two_second_first_fourth :
    homComponent 1 (chernFamily C q Q r) ^ 6 =
      (2 : ℤ) • (homComponent 2 (chernFamily C q Q r) *
        homComponent 1 (chernFamily C q Q r) ^ 4) :=
  first_sixth_eq_two_second_first_fourth _ (chernFamily_apply_zero C q Q r)
    (signed_chern_mul_eq_one C q Q r F i p w hseq e)

end M9Native.SymplecticQuotientChernRelation

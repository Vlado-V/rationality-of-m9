module

public import M9StacksIntegration.GradedCapVirtualSchur
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapSignScale

/-!
# Genuine Whitney recurrence for the inverse Chern family of a kernel

The input is the actual short exact sequence of sheaf modules, with
kernel rank n and quotient rank one. Native Whitney proves the actual
total-Chern product. The middle module's finite local freeness is
derived from the same sequence, and native c0=id proves the actual
Chern units. Cancellation preserves order in the operational cap ring.
No Chern-product, inverse, projective-pushforward or Segre comparison
is supplied as a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.ChowWhitneyKernelInverse
open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
open M9Native.GradedCapVirtualSchur

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q]

/-- For an actual kernel of a rank-one quotient, genuine native Whitney
and native Chern-unit cancellation give c(K)^{-1}=c(L)c(M)^{-1}.
The middle module's rank is derived from the actual short exact row. -/
theorem inverseFamily_kernel_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank S.X₁ n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank S.X₃ 1] :
    haveI := isFiniteLocallyFreeOfRank_of_shortExact S hS n 1 ‹_› ‹_›
    inverseFamily C q S.X₁ n =
      chernFamily C q S.X₃ 1 * inverseFamily C q S.X₂ (n + 1) := by
  let := isFiniteLocallyFreeOfRank_of_shortExact S hS n 1 ‹_› ‹_›
  have hw := chernFamily_eq_mul_of_shortExact C q S hS n 1
  have hm : chernFamily C q S.X₂ (n + 1) * inverseFamily C q S.X₂ (n + 1) = 1 := by
    simp only [inverseFamily, IsUnit.mul_val_inv]
  calc
    inverseFamily C q S.X₁ n = inverseFamily C q S.X₁ n *
        (chernFamily C q S.X₂ (n + 1) * inverseFamily C q S.X₂ (n + 1)) := by
      rw [hm, mul_one]
    _ = ((inverseFamily C q S.X₁ n * chernFamily C q S.X₁ n) *
        chernFamily C q S.X₃ 1) * inverseFamily C q S.X₂ (n + 1) := by
      rw [hw]
      simp only [mul_assoc]
    _ = chernFamily C q S.X₃ 1 * inverseFamily C q S.X₂ (n + 1) := by
      simp only [inverseFamily, IsUnit.val_inv_mul, one_mul]

/-- The same actual kernel recurrence after native degree-sign scaling.
Only the proved native multiplicativity of that scaling is used. -/
theorem signScale_inverseFamily_kernel_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank S.X₁ n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank S.X₃ 1] :
    haveI := isFiniteLocallyFreeOfRank_of_shortExact S hS n 1 ‹_› ‹_›
    capFamilySignScale (inverseFamily C q S.X₁ n) =
      capFamilySignScale (chernFamily C q S.X₃ 1) *
        capFamilySignScale (inverseFamily C q S.X₂ (n + 1)) := by
  let := isFiniteLocallyFreeOfRank_of_shortExact S hS n 1 ‹_› ‹_›
  simpa only [capFamilySignScale_mul] using
    congrArg (fun a : GradedCapFamily (chowGroup C q) => capFamilySignScale a)
      (inverseFamily_kernel_of_shortExact C q S hS n)

end M9Native.ChowWhitneyKernelInverse

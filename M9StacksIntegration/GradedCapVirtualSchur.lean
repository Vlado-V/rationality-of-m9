module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernFamily
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing

/-!
# The actual virtual Chern cap family and ordered Schur operator

The virtual family is the genuine total Chern family of F multiplied by
the inverse of the genuine total Chern family of E. Native c0=id proves
the latter is a unit. All products are the native ordered convolution
of cap operators; no commutativity, Chow exponential or geometric
projective-push comparison is assumed here.

The degree-nine expression retains the literal determinant order
333 - 342 - 423 + 441 + 522 - 531. Its coefficient is expanded into
actual nested cap maps with only the native grading transport.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v
namespace M9Native.GradedCapVirtualSchur
open AlgebraicGeometry CategoryTheory Finset Stacks.Chow
open Stacks.Chow.GenuineChern

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- An ordered triple of actual coefficient maps, with the sole final
native grading transport. The rightmost factor acts first. -/
def coefficientWord3 (a b c : GradedCapFamily G) (i j l n : ℕ)
    (h : i + j + l = n) (k : ℤ) (α : G k) : G (k - (n : ℤ)) :=
  capTo a i (by omega) (b (k - (l : ℤ)) j (c k l α))

/-- A homogeneous right factor leaves exactly its own index in the
native convolution. No condition on the left factor is needed. -/
theorem mul_apply_of_homogeneous_right (a : GradedCapFamily G)
    {b : GradedCapFamily G} {j : ℕ} (hb : b.IsHomogeneous j)
    (i : ℕ) (k : ℤ) (α : G k) :
    (a * b) k (i + j) α =
      capTo a i (by omega) (b k j α) := by
  rw [gradedCap_mul_apply, Finset.sum_eq_single j]
  · rw [convolveTerm_of_le a b k (by omega : j ≤ i + j)]
    rw [capTo_congr_index a (show i + j - j = i by omega)]
  · intro l hl hlj
    rw [convolveTerm_of_le a b k (mem_range_succ_iff.mp hl), hb k l hlj]
    simp only [AddMonoidHom.zero_apply, capTo_zero]
  · intro hj
    exact (hj (mem_range.mpr (by omega))).elim

/-- The product of three selected homogeneous components is exactly
the corresponding ordered coefficient word on every actual input. -/
theorem homComponent_triple_apply (a b c : GradedCapFamily G) (i j l n : ℕ)
    (h : i + j + l = n) (k : ℤ) (α : G k) :
    (homComponent i a * homComponent j b * homComponent l c) k n α =
      coefficientWord3 a b c i j l n h k α := by
  subst n
  rw [mul_apply_of_homogeneous_right _ (isHomogeneous_homComponent l c),
    homComponent_apply_self, capTo_def,
    mul_apply_of_homogeneous_right _ (isHomogeneous_homComponent j b),
    homComponent_apply_self, gradedDegreeCast_capTo, capTo_def,
    homComponent_apply_self]
  rfl

/-- The literal ordered degree-nine Schur expression. This definition
does not replace operator order by commutative scalar multiplication. -/
def schur333 (c : GradedCapFamily G) : GradedCapFamily G :=
  homComponent 3 c * homComponent 3 c * homComponent 3 c -
    homComponent 3 c * homComponent 4 c * homComponent 2 c -
    homComponent 4 c * homComponent 2 c * homComponent 3 c +
    homComponent 4 c * homComponent 4 c * homComponent 1 c +
    homComponent 5 c * homComponent 2 c * homComponent 2 c -
    homComponent 5 c * homComponent 3 c * homComponent 1 c

/-- Every literal ordered term has degree nine, so their signed sum
is genuinely homogeneous of degree nine in the native cap ring. -/
theorem schur333_homogeneous (c : GradedCapFamily G) :
    (schur333 c).IsHomogeneous 9 := by
  have h1 := isHomogeneous_homComponent 1 c
  have h2 := isHomogeneous_homComponent 2 c
  have h3 := isHomogeneous_homComponent 3 c
  have h4 := isHomogeneous_homComponent 4 c
  have h5 := isHomogeneous_homComponent 5 c
  have h333 := (h3.mul h3).mul h3
  have h342 := (h3.mul h4).mul h2
  have h423 := (h4.mul h2).mul h3
  have h441 := (h4.mul h4).mul h1
  have h522 := (h5.mul h2).mul h2
  have h531 := (h5.mul h3).mul h1
  simpa only [schur333, sub_eq_add_neg, neg_one_zsmul] using
    (((((h333.add (h342.zsmul (-1))).add (h423.zsmul (-1))).add h441).add h522).add
      (h531.zsmul (-1)))

/-- The actual degree-nine operator is its own ninth homogeneous
component. -/
theorem schur333_homComponent (c : GradedCapFamily G) :
    homComponent 9 (schur333 c) = schur333 c :=
  (schur333_homogeneous c).homComponent_self

/-- All coefficients away from degree nine vanish. -/
theorem schur333_apply_of_ne (c : GradedCapFamily G) (k : ℤ) (m : ℕ) (hm : m ≠ 9) :
    schur333 c k m = 0 :=
  schur333_homogeneous c k m hm

/-- Exact coefficient-word application of the original ordered Schur
operator, on every genuine graded-group element. -/
theorem schur333_apply (c : GradedCapFamily G) (k : ℤ) (α : G k) :
    schur333 c k 9 α =
      coefficientWord3 c c c 3 3 3 9 (by decide) k α -
        coefficientWord3 c c c 3 4 2 9 (by decide) k α -
        coefficientWord3 c c c 4 2 3 9 (by decide) k α +
        coefficientWord3 c c c 4 4 1 9 (by decide) k α +
        coefficientWord3 c c c 5 2 2 9 (by decide) k α -
        coefficientWord3 c c c 5 3 1 9 (by decide) k α := by
  simp only [schur333, Pi.sub_apply, Pi.add_apply,
    AddMonoidHom.sub_apply, AddMonoidHom.add_apply]
  rw [homComponent_triple_apply c c c 3 3 3 9 (by decide),
    homComponent_triple_apply c c c 3 4 2 9 (by decide),
    homComponent_triple_apply c c c 4 2 3 9 (by decide),
    homComponent_triple_apply c c c 4 4 1 9 (by decide),
    homComponent_triple_apply c c c 5 2 2 9 (by decide),
    homComponent_triple_apply c c c 5 3 1 9 (by decide)]

end Generic

section ActualChow
variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q]

/-- The inverse of the genuine total Chern cap family. Native c0=id
proves the actual unit; no invertibility premise is supplied. -/
def inverseFamily (E : X.Modules) (rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] :
    GradedCapFamily (chowGroup C q) :=
  ↑((isUnit_chernFamily C q E rE).unit⁻¹)

/-- The actual virtual total Chern cap family c(F)c(E)^{-1}. -/
def virtualFamily (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] :
    GradedCapFamily (chowGroup C q) :=
  chernFamily C q F rF * inverseFamily C q E rE

/-- The genuine homogeneous component of the actual virtual family. -/
def virtualComponent (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] (i : ℕ) :
    GradedCapFamily (chowGroup C q) :=
  homComponent i (virtualFamily C q F E rF rE)

/-- The inverse selected by the actual unit is the native recursive
right inverse, by two-sided inverse uniqueness. -/
theorem inverseFamily_eq_gradedRightInv (E : X.Modules) (rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] :
    inverseFamily C q E rE = gradedRightInv (chernFamily C q E rE) := by
  have h := mul_gradedRightInv (chernFamily_apply_zero C q E rE)
  calc
    inverseFamily C q E rE = inverseFamily C q E rE *
        (chernFamily C q E rE * gradedRightInv (chernFamily C q E rE)) := by
      rw [h, mul_one]
    _ = gradedRightInv (chernFamily C q E rE) := by
      rw [← mul_assoc]
      simp only [inverseFamily, IsUnit.val_inv_mul, one_mul]

/-- The actual inverse family has identity constant coefficient. -/
theorem inverseFamily_apply_zero (E : X.Modules) (rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] (k : ℤ) :
    inverseFamily C q E rE k 0 = (1 : GradedCapFamily (chowGroup C q)) k 0 := by
  rw [inverseFamily_eq_gradedRightInv]
  exact gradedRightInv_zero _ k

/-- The genuine inverse coefficients satisfy the actual finite ordered
recurrence; all transports are native grading casts. -/
theorem inverseFamily_recurrence (E : X.Modules) (rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] (k : ℤ) (m : ℕ) :
    inverseFamily C q E rE k m = (1 : GradedCapFamily (chowGroup C q)) k m -
      ∑ j : Fin m, (gradedDegreeCast (chowGroup C q)
        (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
          have := j.isLt; omega)).toAddMonoidHom.comp
        ((chernFamily C q E rE (k - ((j : ℕ) : ℤ)) (m - j)).comp
          (inverseFamily C q E rE k j)) := by
  simpa only [inverseFamily_eq_gradedRightInv] using
    gradedRightInv_apply (chernFamily C q E rE) k m

/-- Cancellation retains the original operator order. -/
theorem virtualFamily_mul_chern (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] :
    virtualFamily C q F E rF rE * chernFamily C q E rE = chernFamily C q F rF := by
  simp only [virtualFamily, inverseFamily, mul_assoc, IsUnit.val_inv_mul, mul_one]

/-- Actual virtual coefficients are the finite convolution of actual
Chern caps and actual recursive inverse caps, not scalar replacements. -/
theorem virtualFamily_apply (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] (k : ℤ) (m : ℕ)
    (α : chowGroup C q k) :
    virtualFamily C q F E rF rE k m α =
      ∑ j : Fin (m + 1), capTo (chernFamily C q F rF) (m - j)
        (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
          have := j.isLt; omega) (inverseFamily C q E rE k j α) := by
  rw [virtualFamily, gradedCap_mul_apply,
    ← Fin.sum_univ_eq_sum_range
      (fun j => convolveTerm (chernFamily C q F rF) (inverseFamily C q E rE) k m j α) (m + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact convolveTerm_of_le _ _ _ (by have := j.isLt; omega) α

/-- The selected actual virtual component retains exactly its own
coefficient on each original Chow group. -/
theorem virtualComponent_apply_self (F E : X.Modules) (rF rE : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank F rF]
    [SheafOfModules.IsFiniteLocallyFreeOfRank E rE] (i : ℕ) (k : ℤ) :
    virtualComponent C q F E rF rE i k i = virtualFamily C q F E rF rE k i :=
  homComponent_apply_self i _ k

end ActualChow
end M9Native.GradedCapVirtualSchur

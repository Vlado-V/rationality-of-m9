module

public import M9StacksIntegration.LineFamilyCapWords
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Map
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap

/-!
# Actual line-family powers are genuine native cap powers

The original line-family word theorem, applied to a literal replicated
list, identifies its only nonzero coefficient with the actual native
iterated cap. The proved native constant-list comparison gives capPow
of the SAME invertible line. All grade changes are genuine native casts.
No cap identity or action compatibility is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LineFamilyCapPower

open Stacks.Chow ChowCapWords GradedLineCapSubring LineFamilyCapWords

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q]

theorem familyWord_replicate (L : InvertibleLine X) (a : ℕ) :
    familyWord C q (List.replicate a L) = lineFamily C q L ^ a := by
  simp only [familyWord, List.map_replicate, List.prod_replicate]

/-- The component of the actual operational power is the native capPow
of the original line, with only dependent output-grade transport. -/
theorem lineFamily_pow_apply_heq (L : InvertibleLine X) (a : ℕ) (k m : ℤ)
    (h : k = m + (a : ℤ)) (α : chowGroup C q k) :
    (lineFamily C q L ^ a) k a α ≍ capPow C q (lineCap C q L) a k m h α := by
  let Ls := List.replicate a L
  have hlen : Ls.length = a := by simp only [Ls, List.length_replicate]
  have hOs : Ls.map (lineCap C q) = List.replicate a (lineCap C q L) := by
    simp only [Ls, List.map_replicate]
  have eW : k = m + ((Ls.map (lineCap C q)).length : ℤ) := by
    simpa only [List.length_map, hlen] using h
  have eP : k = m + ((List.replicate a (lineCap C q L)).length : ℤ) := by
    simpa only [List.length_replicate] using h
  let βW := chowGroupCast C q eW α
  let βP := chowGroupCast C q eP α
  have hStart : (lineFamily C q L ^ a) k a α ≍ familyWord C q Ls k Ls.length α := by
    have hRep := congrArg (fun A : GradedCapFamily (chowGroup C q) => A k a α)
      (familyWord_replicate C q L a)
    exact (heq_of_eq hRep).symm.trans
      (family_apply_index_heq C q (familyWord C q Ls) k hlen.symm α)
  have hWord := familyWord_apply_heq C q Ls
    (show k - (Ls.length : ℤ) = m by rw [hlen]; omega)
    (α := α) (β := βW) (chowGroupCast_heq C q eW α).symm
  have hIter := iteratedChernCapOnChow_heq_of_eq C q hOs m
    (x := βW) (y := βP)
    ((chowGroupCast_heq C q eW α).trans (chowGroupCast_heq C q eP α).symm)
  have hPower := capPow_eq_iteratedChernCapOnChow C q (lineCap C q L) a m βP
  have hCast : capPow C q (lineCap C q L) a
      (m + ((List.replicate a (lineCap C q L)).length : ℤ)) m (by simp) βP =
      capPow C q (lineCap C q L) a k m h α :=
    capPow_cast C q (lineCap C q L) a m (by simp) eP α
  exact hStart.trans (hWord.trans (hIter.trans
    ((heq_of_eq hPower.symm).trans (heq_of_eq hCast))))

/-- In the native output grade k-a the comparison is an actual equality. -/
theorem lineFamily_pow_apply (L : InvertibleLine X) (a : ℕ) (k : ℤ)
    (α : chowGroup C q k) :
    (lineFamily C q L ^ a) k a α =
      capPow C q (lineCap C q L) a k (k-(a:ℤ)) (by omega) α :=
  eq_of_heq (lineFamily_pow_apply_heq C q L a k (k-(a:ℤ)) (by omega) α)

/-- An arbitrary equal output grade uses exactly the original native degree cast. -/
theorem gradedDegreeCast_lineFamily_pow_apply (L : InvertibleLine X) (a : ℕ) (k m : ℤ)
    (h : k = m + (a : ℤ)) (α : chowGroup C q k) :
    gradedDegreeCast (chowGroup C q) (show k-(a:ℤ)=m by omega)
      ((lineFamily C q L ^ a) k a α) = capPow C q (lineCap C q L) a k m h α :=
  eq_of_heq ((gradedDegreeCast_heq _ _).trans (lineFamily_pow_apply_heq C q L a k m h α))

end M9Native.LineFamilyCapPower

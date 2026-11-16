module

public import M9StacksIntegration.GradedLineCapSubring

/-!
# Actual graded line-family products are actual native cap words

Each factor is the original native first-Chern cap of an actual
invertible module. All changes of Chow degree use the native casts;
the comparison holds on every actual input class in equal grades.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LineFamilyCapWords

open Stacks.Chow ChowCapWords GradedLineCapSubring GradedCapVirtualSchur

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q]

def familyWord (Ls : List (InvertibleLine X)) : GradedCapFamily (chowGroup C q) :=
  (Ls.map (lineFamily C q)).prod

theorem familyWord_homogeneous (Ls : List (InvertibleLine X)) :
    (familyWord C q Ls).IsHomogeneous Ls.length := by
  induction Ls with
  | nil => exact GradedCapFamily.IsHomogeneous.one
  | cons L Ls ih =>
      simpa only [familyWord, List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm]
        using (lineFamily_homogeneous C q L).mul ih

theorem family_apply_index_heq (a : GradedCapFamily (chowGroup C q)) (k : ℤ)
    {i j : ℕ} (h : i = j) (α : chowGroup C q k) : a k i α ≍ a k j α := by
  subst j
  rfl

theorem familyWord_apply_heq (Ls : List (InvertibleLine X)) {k d : ℤ}
    (hd : k - (Ls.length : ℤ) = d) {α : chowGroup C q k}
    {β : chowGroup C q (d + ((Ls.map (lineCap C q)).length : ℤ))} (hα : α ≍ β) :
    familyWord C q Ls k Ls.length α ≍
      iteratedChernCapOnChow C q (Ls.map (lineCap C q)) d β := by
  induction Ls generalizing k d with
  | nil =>
      simp only [familyWord, List.map_nil, List.prod_nil, List.length_nil]
      rw [gradedCap_one_apply_zero]
      exact (gradedDegreeCast_heq _ α).trans
        (hα.trans (iteratedChernCapOnChow_nil_heq C q d β).symm)
  | cons L Ls ih =>
      let Os := Ls.map (lineCap C q)
      let O := lineCap C q L
      have hdTail : k - (Ls.length : ℤ) = d + 1 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hd
        omega
      have hβgrade : d + (((L :: Ls).map (lineCap C q)).length : ℤ) =
          d + 1 + (Os.length : ℤ) := by
        simp only [Os, List.length_map, List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      let β' := chowGroupCast C q hβgrade β
      have hβ : β' ≍ β := chowGroupCast_heq C q hβgrade β
      have hTail := ih (k := k) (d := d + 1) hdTail (α := α) (β := β') (hα.trans hβ.symm)
      have hLine := lineFamily_apply_heq C q L (k := k - (Ls.length : ℤ)) (d := d)
        (by omega) hTail
      have hProd : familyWord C q (L :: Ls) = lineFamily C q L * familyWord C q Ls := by
        simp only [familyWord, List.map_cons, List.prod_cons]
      have hValue := congrArg (fun a : GradedCapFamily (chowGroup C q) =>
        a k (L :: Ls).length α) hProd
      have hIndex := family_apply_index_heq C q
        (lineFamily C q L * familyWord C q Ls) k
        (show (L :: Ls).length = 1 + Ls.length by simp [Nat.add_comm]) α
      have hMul := mul_apply_of_homogeneous_right (lineFamily C q L)
        (familyWord_homogeneous C q Ls) 1 k α
      have hCast : (k - (Ls.length : ℤ)) - (1 : ℤ) = k - ((1 + Ls.length : ℕ) : ℤ) := by
        omega
      have hDrop : capTo (lineFamily C q L) 1 hCast
          (familyWord C q Ls k Ls.length α) ≍
          lineFamily C q L (k - (Ls.length : ℤ)) 1
            (familyWord C q Ls k Ls.length α) :=
        gradedDegreeCast_heq _ _
      have hCons := iteratedChernCapOnChow_cons_eq C q O Os d β β' hβ.symm
      exact (heq_of_eq hValue).trans (hIndex.trans
        ((heq_of_eq hMul).trans (hDrop.trans (hLine.trans (heq_of_eq hCons).symm))))

end M9Native.LineFamilyCapWords

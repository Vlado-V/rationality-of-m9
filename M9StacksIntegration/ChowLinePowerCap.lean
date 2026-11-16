module

public import M9StacksIntegration.LineFamilyCapWords
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree

/-! # Powers of the actual line family are the original iterated first-Chern caps -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.ChowLinePowerCap

open ChowCapWords GradedLineCapSubring LineFamilyCapWords

/-- A constant word is the actual power in the original ordered cap ring. -/
theorem familyWord_replicate (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (L : InvertibleLine X) (n : ℕ) :
    familyWord C q (List.replicate n L) = lineFamily C q L ^ n := by
  simp only [familyWord, List.map_replicate, List.prod_replicate]

/-- The same geometric caps, with only the native integer grading transport. -/
theorem lineFamily_pow_heq_iteratedFirstChernCap (K : Type u) [Field K]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of K)) [IsProper q]
    (L : InvertibleLine X) (n : ℕ)
    (α : chowGroup (fieldChowSituation K) q n) :
    let _ : ∀ j : Fin n,
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L.val := fun _ => L.property
    (lineFamily (fieldChowSituation K) q L ^ n) n n α ≍
      iteratedFirstChernCap K q (fun _ : Fin n => L.val) α := by
  let _ : ∀ j : Fin n,
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L.val := fun _ => L.property
  let _ : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L.val := L.property
  let Ls := List.replicate n L
  let β := chowGroupCast (fieldChowSituation K) q
    (show (n : ℤ) = 0 + ((Ls.map (lineCap (fieldChowSituation K) q)).length : ℤ) by
      simp [Ls]) α
  have h := familyWord_apply_heq (fieldChowSituation K) q Ls
    (k := n) (d := 0) (by simp [Ls]) (α := α) (β := β)
    (chowGroupCast_heq (fieldChowSituation K) q _ α).symm
  have hword := congrArg (fun A : GradedCapFamily (chowGroup (fieldChowSituation K) q) =>
      A n Ls.length α) (familyWord_replicate (fieldChowSituation K) q L n)
  have hindex := family_apply_index_heq (fieldChowSituation K) q
    (lineFamily (fieldChowSituation K) q L ^ n) n
    (show Ls.length = n by simp [Ls]) α
  let Os := List.ofFn (fun _ : Fin n => invCap (fieldChowSituation K) q L.val)
  let γ := chowGroupCast (fieldChowSituation K) q
    (show (n : ℤ) = 0 + (Os.length : ℤ) by simp [Os]) α
  have hOs : Ls.map (lineCap (fieldChowSituation K) q) = Os := by
    simp [Ls, Os, lineCap]
  have hright := iteratedChernCapOnChow_heq_of_eq
    (fieldChowSituation K) q hOs 0 (x := β) (y := γ)
    ((chowGroupCast_heq (fieldChowSituation K) q _ α).trans
      (chowGroupCast_heq (fieldChowSituation K) q _ α).symm)
  exact hindex.symm.trans ((heq_of_eq hword).symm.trans (h.trans hright))

end M9Native.ChowLinePowerCap

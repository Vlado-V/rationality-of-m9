module

public import M9StacksIntegration.CurveSingleCapDegree
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor

/-!
# Actual symmetric words of first Chern caps

The operations are the native Chow cap operators of actual invertible
modules. Their commutativity is the proved native Stacks 02TJ theorem.
List permutations only transport the actual integer grading; they do
not introduce a symmetric intersection functional as an assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace M9Native.ChowCapWords

open Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]

theorem identityCycle_eq_zero_of_genericDimension_ne [IsIntegral X] (d : ℤ)
    (hd : relativeDimension C.dimensionFunction f (genericPoint X) ≠ d) :
    cycleAssociatedToClosedSubscheme C f (𝟙 X) d = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (cycleAssociatedToClosedSubscheme C f (𝟙 X) d).1 x = 0
  apply cycleAssociatedToClosedSubscheme_apply_eq_zero C f (𝟙 X) d x
  rintro ⟨ξ, hξx, hξd⟩
  have hξ : (ξ : X) = genericPoint X := by
    have hmem : (ξ : X) ∈ ({genericPoint X} : Set X) := by
      rw [← genericPoints_eq_singleton]
      exact ξ.2
    exact hmem
  have hx : x = genericPoint X := hξx.symm.trans hξ
  exact hd (hx ▸ hξd)

theorem identityChowClass_eq_zero_of_genericDimension_ne [IsIntegral X] (d : ℤ)
    (hd : relativeDimension C.dimensionFunction f (genericPoint X) ≠ d) :
    CurveTopChowClass.identityChowClass C f d = 0 := by
  change (QuotientAddGroup.mk' (rationalEquivalences C f d))
    (cycleAssociatedToClosedSubscheme C f (𝟙 X) d) = 0
  rw [identityCycle_eq_zero_of_genericDimension_ne C f d hd, map_zero]

theorem iterated_cons_cons_eq (O P : ChernCapOperator C f)
    (Os : List (ChernCapOperator C f)) (d : ℤ)
    (x : chowGroup C f (d + ((O :: P :: Os).length : ℤ)))
    (y : chowGroup C f (d + 1 + 1 + (Os.length : ℤ))) (hxy : x ≍ y) :
    iteratedChernCapOnChow C f (O :: P :: Os) d x =
      O.capOnChow C f d (P.capOnChow C f (d + 1)
        (iteratedChernCapOnChow C f Os (d + 1 + 1) y)) := by
  let x' : chowGroup C f (d + 1 + ((P :: Os).length : ℤ)) :=
    chowGroupCast C f (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring) x
  rw [iteratedChernCapOnChow_cons_eq C f O (P :: Os) d x x'
    (chowGroupCast_heq C f _ x).symm]
  rw [iteratedChernCapOnChow_cons_eq C f P Os (d + 1) x' y
    ((chowGroupCast_heq C f _ x).trans hxy)]

theorem iterated_map_eq_of_perm {α : Type v} (O : α → ChernCapOperator C f)
    (hcomm : ∀ a b (d : ℤ) (z : chowGroup C f (d + 1 + 1)),
      (O a).capOnChow C f d ((O b).capOnChow C f (d + 1) z) =
        (O b).capOnChow C f d ((O a).capOnChow C f (d + 1) z))
    {as bs : List α} (hab : as.Perm bs) (d : ℤ)
    (x : chowGroup C f (d + ((as.map O).length : ℤ)))
    (y : chowGroup C f (d + ((bs.map O).length : ℤ))) (hxy : x ≍ y) :
    iteratedChernCapOnChow C f (as.map O) d x =
      iteratedChernCapOnChow C f (bs.map O) d y := by
  induction hab generalizing d with
  | nil =>
      exact chowGroup_eq_of_heq C f ((iteratedChernCapOnChow_nil_heq C f d x).trans
        (hxy.trans (iteratedChernCapOnChow_nil_heq C f d y).symm))
  | @cons a as bs hab ih =>
      change iteratedChernCapOnChow C f (O a :: as.map O) d x =
        iteratedChernCapOnChow C f (O a :: bs.map O) d y
      let x' : chowGroup C f (d + 1 + ((as.map O).length : ℤ)) :=
        chowGroupCast C f (by simp only [List.map_cons, List.length_cons,
          Nat.cast_add, Nat.cast_one]; ring) x
      let y' : chowGroup C f (d + 1 + ((bs.map O).length : ℤ)) :=
        chowGroupCast C f (by simp only [List.map_cons, List.length_cons,
          Nat.cast_add, Nat.cast_one]; ring) y
      rw [iteratedChernCapOnChow_cons_eq C f (O a) (as.map O) d x x'
        (chowGroupCast_heq C f _ x).symm,
        iteratedChernCapOnChow_cons_eq C f (O a) (bs.map O) d y y'
        (chowGroupCast_heq C f _ y).symm]
      congr 1
      exact ih (d + 1) x' y'
        ((chowGroupCast_heq C f _ x).trans (hxy.trans (chowGroupCast_heq C f _ y).symm))
  | swap a b as =>
      change iteratedChernCapOnChow C f (O b :: O a :: as.map O) d x =
        iteratedChernCapOnChow C f (O a :: O b :: as.map O) d y
      let z : chowGroup C f (d + 1 + 1 + ((as.map O).length : ℤ)) :=
        chowGroupCast C f (by simp only [List.map_cons, List.length_cons,
          Nat.cast_add, Nat.cast_one]; ring) x
      rw [iterated_cons_cons_eq C f (O b) (O a) (as.map O) d x z
        (chowGroupCast_heq C f _ x).symm,
        iterated_cons_cons_eq C f (O a) (O b) (as.map O) d y z
        (hxy.symm.trans (chowGroupCast_heq C f _ x).symm)]
      exact hcomm b a d _
  | @trans as bs cs hab hbc ih₁ ih₂ =>
      have hd : d + ((as.map O).length : ℤ) = d + ((bs.map O).length : ℤ) := by
        simp only [List.length_map]
        rw [hab.length_eq]
      let z := chowGroupCast C f hd x
      exact (ih₁ d x z (chowGroupCast_heq C f hd x).symm).trans
        (ih₂ d z y ((chowGroupCast_heq C f hd x).trans hxy))

abbrev InvertibleLine (X : Scheme.{u}) : Type (u + 1) :=
  {L : X.Modules // SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L}

def lineCap (L : InvertibleLine X) : ChernCapOperator C f :=
  @invCap C X f _ L.1 L.2

theorem lineCap_comm (L M : InvertibleLine X) (d : ℤ)
    (a : chowGroup C f (d + 1 + 1)) :
    (lineCap C f L).capOnChow C f d ((lineCap C f M).capOnChow C f (d + 1) a) =
      (lineCap C f M).capOnChow C f d ((lineCap C f L).capOnChow C f (d + 1) a) := by
  let := L.2
  let := M.2
  exact GenuineChern.invCap_capOnChow_comm C f d L.1 M.1 a

theorem iterated_lineCaps_eq_of_perm {Ls Ms : List (InvertibleLine X)} (h : Ls.Perm Ms)
    (d : ℤ) (x : chowGroup C f (d + ((Ls.map (lineCap C f)).length : ℤ)))
    (y : chowGroup C f (d + ((Ms.map (lineCap C f)).length : ℤ))) (hxy : x ≍ y) :
    iteratedChernCapOnChow C f (Ls.map (lineCap C f)) d x =
      iteratedChernCapOnChow C f (Ms.map (lineCap C f)) d y :=
  iterated_map_eq_of_perm C f (lineCap C f) (lineCap_comm C f) h d x y hxy

theorem invCap_congr (L M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : L ≅ M) (d : ℤ) (a : chowGroup C f (d + 1)) :
    (invCap C f L).capOnChow C f d a = (invCap C f M).capOnChow C f d a := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  rw [invCap_capOnChow_mk, invCap_capOnChow_mk]
  exact firstChernClassCapOfInvertible_congr C f d L M e b

end M9Native.ChowCapWords

module

public import M9StacksIntegration.CurvePowerGraphBaseChange
public import M9StacksIntegration.CurvePowerConstantClass

/-!
# Actual restrictions of the graph lines on curve powers

All classes are the literal actual graph-family classes of the checked
Cartier provider. The two-coordinate class is its literal degree-one
graph on the square, including when the two selected coordinates agree.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphRestrictions

open CurvePowerGraphCartier (graphClass graphSection)
open CurvePowerGraphBaseChange (extendIndex)

variable {S : Scheme.{u}} (C : Over S)

/-- The actual graph, regarded as a morphism over the original base. -/
def graphOver (m : ℕ) (y : power C m ⟶ C) : power C m ⟶ power C (m + 1) :=
  Over.homMk (graphSection C m y) (CurvePowerGraphBaseChange.graphSection_comp_hom C m y)

@[simp] theorem graphOver_left (m : ℕ) (y : power C m ⟶ C) :
    (graphOver C m y).left = graphSection C m y := rfl

@[reassoc] theorem graphOver_fst (m : ℕ) (y : power C m ⟶ C) :
    graphOver C m y ≫ fst C (power C m) = y := by
  apply Over.OverMorphism.ext
  exact Stacks.Hilbert.pointGraph_comp_fst C (power C m) y

@[reassoc] theorem graphOver_snd (m : ℕ) (y : power C m ⟶ C) :
    graphOver C m y ≫ snd C (power C m) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Stacks.Hilbert.pointGraph_comp_snd C (power C m) y

@[reassoc] theorem graphOver_coord_zero (m : ℕ) (y : power C m ⟶ C) :
    graphOver C m y ≫ coord C (m + 1) 0 = y := by
  simpa only [coord_zero] using graphOver_fst C m y

@[reassoc] theorem graphOver_coord_succ (m : ℕ) (y : power C m ⟶ C) (i : Fin m) :
    graphOver C m y ≫ coord C (m + 1) i.succ = coord C m i := by
  rw [coord_succ, ← Category.assoc, graphOver_snd, Category.id_comp]

abbrev coordinateMap (m : ℕ) (i : Fin m) : power C m ⟶ power C 1 :=
  reindex C (fun _ : Fin 1 => i)

abbrev firstMap (m : ℕ) : power C (m + 1) ⟶ power C 1 :=
  reindex C (fun _ : Fin 1 => 0)

abbrev diagonalClass [IsSeparated C.hom] [SmoothOfRelativeDimension 1 C.hom] :
    Stacks.Picard.ofScheme (power C 2).left := graphClass C 1 (coord C 1 0)

abbrev pointClass [IsSeparated C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (c₀ : power C 0 ⟶ C) : Stacks.Picard.ofScheme (power C 1).left := graphClass C 0 c₀

theorem graphOver_reindex_coordinate (m : ℕ) (i j : Fin m) :
    graphOver C m (coord C m i) ≫ reindex C (extendIndex (fun _ : Fin 1 => j)) =
      reindex C ![i,j] := by
  apply Stacks.CurvePower.hom_ext 2
  intro a
  rw [Category.assoc, reindex_coord, reindex_coord]
  fin_cases a
  · change graphOver C m (coord C m i) ≫ coord C (m + 1) 0 = coord C m i
    exact graphOver_coord_zero C m _
  · change graphOver C m (coord C m i) ≫ coord C (m + 1) j.succ = coord C m j
    exact graphOver_coord_succ C m _ j

theorem graphOver_first (m : ℕ) (y : power C m ⟶ C) :
    graphOver C m y ≫ firstMap C m = lift 1 (fun _ => y) := by
  apply Stacks.CurvePower.hom_ext 1
  intro a
  rw [Category.assoc,reindex_coord,lift_coord]
  exact graphOver_coord_zero C m y

variable [IsSeparated C.hom] [SmoothOfRelativeDimension 1 C.hom]

theorem coordinate_graphClass (m : ℕ) (j : Fin m) :
    graphClass C m (coord C m j) =
      Stacks.Picard.schemePullbackClass (reindex C (extendIndex (fun _ : Fin 1 => j))).left
        (diagonalClass C) := by
  have h := CurvePowerGraphBaseChange.graphClass_pullback_reindex_extend C
    (fun _ : Fin 1 => j) (coord C 1 0)
  simpa only [reindex_coord] using h.symm

/-- This is the actual literal diagonal-pullback class for all `i,j`,
 including the actual self-line when `i=j`. -/
theorem coordinate_graphClass_restrict_coordinate (m : ℕ) (i j : Fin m) :
    Stacks.Picard.schemePullbackClass (graphSection C m (coord C m i))
      (graphClass C m (coord C m j)) =
    Stacks.Picard.schemePullbackClass (reindex C ![i,j]).left (diagonalClass C) := by
  rw [coordinate_graphClass, Stacks.Picard.schemePullbackClass_comp]
  change Stacks.Picard.schemePullbackClass
    ((graphOver C m (coord C m i)).left ≫
      (reindex C (extendIndex (fun _ : Fin 1 => j))).left) (diagonalClass C) = _
  rw [← Over.comp_left, graphOver_reindex_coordinate]

theorem constant_graphClass (c₀ : power C 0 ⟶ C) (m : ℕ) :
    graphClass C m (toUnit (power C m) ≫ c₀) =
      Stacks.Picard.schemePullbackClass (firstMap C m).left (pointClass C c₀) := by
  have h := CurvePowerGraphBaseChange.graphClass_pullback_reindex_extend C
    (Fin.elim0 : Fin 0 → Fin m) c₀
  have hz : reindex C (Fin.elim0 : Fin 0 → Fin m) = toUnit (power C m) := toUnit_unique _ _
  have hm : reindex C (extendIndex (Fin.elim0 : Fin 0 → Fin m)) = firstMap C m := by
    congr 1
    funext a
    fin_cases a
    rfl
  rw [hz,hm] at h
  exact h.symm

/-- The actual fixed graph restricted to an actual moving coordinate
 graph is the actual coordinate point-line class. -/
theorem constant_graphClass_restrict_coordinate (c₀ : power C 0 ⟶ C)
    (m : ℕ) (i : Fin m) :
    Stacks.Picard.schemePullbackClass (graphSection C m (coord C m i))
      (graphClass C m (toUnit (power C m) ≫ c₀)) =
    Stacks.Picard.schemePullbackClass (coordinateMap C m i).left (pointClass C c₀) := by
  rw [constant_graphClass, Stacks.Picard.schemePullbackClass_comp]
  change Stacks.Picard.schemePullbackClass
    ((graphOver C m (coord C m i)).left ≫ (firstMap C m).left) (pointClass C c₀) = _
  rw [← Over.comp_left,graphOver_first]
  congr 1

section Field

variable {k : Type u} [Field k] (D : Over (Spec (.of k)))
  [IsSeparated D.hom] [SmoothOfRelativeDimension 1 D.hom]

theorem constant_graphClass_restrict_constant (c₀ : power D 0 ⟶ D) (m : ℕ) :
    Stacks.Picard.schemePullbackClass (graphSection D m (toUnit (power D m) ≫ c₀))
      (graphClass D m (toUnit (power D m) ≫ c₀)) = 0 := by
  rw [CurvePowerGraphCartier.graph_self_class]
  have h := CurvePowerConstantClass.pullback_via_field_zero k
    (toUnit (power D m)).left c₀.left
    (Stacks.SheafOfModules.picardClass D.left.presheaf D.left.ringCatIsSheaf
      (Scheme.Hom.relativeDifferentials D.hom)
      (DiagonalNormalPicard.differentials_isInvertible D.hom))
  exact (congrArg Neg.neg h).trans (neg_zero : -(0 : Stacks.Picard.ofScheme (power D m).left) = 0)

end Field

end M9Native.CurvePowerGraphRestrictions

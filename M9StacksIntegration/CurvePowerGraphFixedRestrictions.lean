module

public import M9StacksIntegration.CurvePowerGraphRestrictions

/-!
# Actual moving graph lines restricted to the fixed section

The diagonal ideal is invariant under the literal swap. The fixed section,
after this swap, is the actual base-change map of the actual point. Thus
its diagonal restriction is the actual point line, and this identity pulls
back to every coordinate on an actual curve power.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphFixedRestrictions

open CurvePowerGraphRestrictions
open CurvePowerGraphCartier (graphClass graphSection)
open CurvePowerGraphBaseChange (extendIndex)

/-- The kernel of an actual closed immersion is unchanged by an actual
ambient automorphism fixing that immersion. -/
theorem ker_comap_of_comp_eq {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (e : Y ⟶ Y) [IsIso e] (h : i ≫ e = i) :
    i.ker.comap e = i.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i e]
  have w : i ≫ e = 𝟙 Z ≫ i := by rw [h, Category.id_comp]
  have hl : pullback.lift i (𝟙 Z) w ≫ pullback.snd e i = 𝟙 Z :=
    pullback.lift_snd _ _ _
  have : IsIso (pullback.lift i (𝟙 Z) w ≫ pullback.snd e i) := by
    rw [hl]
    infer_instance
  have : IsIso (pullback.lift i (𝟙 Z) w) := IsIso.of_isIso_comp_right _ (pullback.snd e i)
  rw [← Scheme.Hom.ker_comp_of_isIso (pullback.lift i (𝟙 Z) w) (pullback.fst e i),
    pullback.lift_fst]

variable {S : Scheme.{u}} (C : Over S)

abbrev swapTwo : power C 2 ⟶ power C 2 :=
  reindex C (Equiv.swap (0 : Fin 2) 1)

theorem swapTwo_square : swapTwo C ≫ swapTwo C = 𝟙 _ := by
  rw [reindex_comp]
  have h : (Equiv.swap (0 : Fin 2) 1) ∘ (Equiv.swap (0 : Fin 2) 1) = id := by
    funext i
    exact Equiv.swap_apply_self _ _ i
  rw [h,reindex_id]

def swapTwoIso : power C 2 ≅ power C 2 where
  hom := swapTwo C
  inv := swapTwo C
  hom_inv_id := swapTwo_square C
  inv_hom_id := swapTwo_square C

instance swapTwo_left_isIso : IsIso (swapTwo C).left := by
  have : IsIso (swapTwo C) := (swapTwoIso C).isIso_hom
  exact inferInstanceAs (IsIso ((Over.forget S).map (swapTwo C)))

theorem diagonalGraph_comp_swap :
    graphOver C 1 (coord C 1 0) ≫ swapTwo C = graphOver C 1 (coord C 1 0) := by
  apply Stacks.CurvePower.hom_ext 2
  intro i
  rw [Category.assoc,reindex_coord]
  fin_cases i
  · change graphOver C 1 (coord C 1 0) ≫ coord C 2 (0 : Fin 1).succ =
      graphOver C 1 (coord C 1 0) ≫ coord C 2 0
    exact (graphOver_coord_succ C 1 _ 0).trans (graphOver_coord_zero C 1 _).symm
  · change graphOver C 1 (coord C 1 0) ≫ coord C 2 0 =
      graphOver C 1 (coord C 1 0) ≫ coord C 2 (0 : Fin 1).succ
    exact (graphOver_coord_zero C 1 _).trans (graphOver_coord_succ C 1 _ 0).symm

variable [IsSeparated C.hom] [SmoothOfRelativeDimension 1 C.hom]

theorem diagonalIdeal_comap_swap :
    (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0)).comap (swapTwo C).left =
      Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0) := by
  letI := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 1)
    (coord C 1 0)
  apply ker_comap_of_comp_eq
  change (graphOver C 1 (coord C 1 0)).left ≫ (swapTwo C).left = _
  rw [← Over.comp_left,diagonalGraph_comp_swap]
  rfl

theorem diagonalClass_pullback_swap :
    Stacks.Picard.schemePullbackClass (swapTwo C).left (diagonalClass C) =
      diagonalClass C := by
  apply Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass
    (GraphNormalPicard.graphFamily C (power C 1) (coord C 1 0))
    (GraphNormalPicard.graphFamily C (power C 1) (coord C 1 0))
  exact (diagonalIdeal_comap_swap C).symm

variable (c₀ : power C 0 ⟶ C)

abbrev pointOne : power C 0 ⟶ power C 1 := lift 1 (fun _ => c₀)

theorem fixedGraph_comp_swap :
    (graphOver C 1 (toUnit (power C 1) ≫ c₀)).left ≫ (swapTwo C).left =
      Stacks.Hilbert.familyBaseChangeMap C (pointOne C c₀) := by
  have h : graphOver C 1 (toUnit (power C 1) ≫ c₀) ≫ swapTwo C =
      CartesianMonoidalCategory.lift (fst C (power C 0))
        (snd C (power C 0) ≫ pointOne C c₀) := by
    apply Stacks.CurvePower.hom_ext 2
    intro i
    rw [Category.assoc,reindex_coord]
    fin_cases i
    · change graphOver C 1 _ ≫ coord C 2 (0 : Fin 1).succ =
        CartesianMonoidalCategory.lift (fst C (power C 0))
          (snd C (power C 0) ≫ pointOne C c₀) ≫ coord C 2 0
      rw [graphOver_coord_succ]
      exact (lift_fst _ _).symm
    · change graphOver C 1 _ ≫ coord C 2 0 =
        CartesianMonoidalCategory.lift (fst C (power C 0))
          (snd C (power C 0) ≫ pointOne C c₀) ≫ coord C 2 (0 : Fin 1).succ
      rw [graphOver_coord_zero]
      change _ = CartesianMonoidalCategory.lift _ _ ≫ snd C (power C 1) ≫ coord C 1 0
      rw [lift_snd_assoc,Category.assoc,lift_coord]
      congr 1
      exact toUnit_unique _ _
  rw [← Over.comp_left,h]
  rfl

/-- The literal diagonal line restricts to the literal point line. -/
theorem diagonalClass_restrict_fixed :
    Stacks.Picard.schemePullbackClass
      (graphSection C 1 (toUnit (power C 1) ≫ c₀)) (diagonalClass C) =
      pointClass C c₀ := by
  rw [← diagonalClass_pullback_swap C, Stacks.Picard.schemePullbackClass_comp]
  change Stacks.Picard.schemePullbackClass
    ((graphOver C 1 (toUnit (power C 1) ≫ c₀)).left ≫ (swapTwo C).left)
      (diagonalClass C) = _
  rw [fixedGraph_comp_swap]
  have hc : Stacks.Picard.schemePullbackClass
      (Stacks.Hilbert.familyBaseChangeMap C (pointOne C c₀)) (diagonalClass C) =
      graphClass C 0 (pointOne C c₀ ≫ coord C 1 0) := by
    letI := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C 1)
      (coord C 1 0)
    apply Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass
      (GraphNormalPicard.graphFamily C (power C 1) (coord C 1 0))
      (GraphNormalPicard.graphFamily C (power C 0) (pointOne C c₀ ≫ coord C 1 0))
    exact (Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap C (pointOne C c₀)
      (coord C 1 0)).symm
  simpa only [pointOne,lift_coord] using hc

theorem fixedGraph_reindex_coordinate (m : ℕ) (j : Fin m) :
    graphOver C m (toUnit (power C m) ≫ c₀) ≫
        reindex C (extendIndex (fun _ : Fin 1 => j)) =
      coordinateMap C m j ≫ graphOver C 1 (toUnit (power C 1) ≫ c₀) := by
  apply Stacks.CurvePower.hom_ext 2
  intro i
  rw [Category.assoc,reindex_coord,Category.assoc]
  fin_cases i
  · change graphOver C m _ ≫ coord C (m + 1) 0 =
      coordinateMap C m j ≫ graphOver C 1 _ ≫ coord C 2 0
    simp only [graphOver_coord_zero,Category.assoc]
    have hz : coordinateMap C m j ≫ toUnit (power C 1) = toUnit (power C m) :=
      toUnit_unique _ _
    rw [← Category.assoc,hz]
  · change graphOver C m _ ≫ coord C (m + 1) j.succ =
      coordinateMap C m j ≫ graphOver C 1 _ ≫ coord C 2 (0 : Fin 1).succ
    rw [graphOver_coord_succ,graphOver_coord_succ]
    exact (reindex_coord (C := C) (fun _ : Fin 1 => j) 0).symm

/-- Every actual moving graph line restricted to the actual fixed
section is the actual coordinate point-line class. -/
theorem coordinate_graphClass_restrict_constant (m : ℕ) (j : Fin m) :
    Stacks.Picard.schemePullbackClass
      (graphSection C m (toUnit (power C m) ≫ c₀))
      (graphClass C m (coord C m j)) =
    Stacks.Picard.schemePullbackClass (coordinateMap C m j).left (pointClass C c₀) := by
  rw [coordinate_graphClass,Stacks.Picard.schemePullbackClass_comp]
  change Stacks.Picard.schemePullbackClass
    ((graphOver C m (toUnit (power C m) ≫ c₀)).left ≫
      (reindex C (extendIndex (fun _ : Fin 1 => j))).left) (diagonalClass C) = _
  rw [← Over.comp_left,fixedGraph_reindex_coordinate,Over.comp_left,
    ← Stacks.Picard.schemePullbackClass_comp]
  exact congrArg (Stacks.Picard.schemePullbackClass (coordinateMap C m j).left)
    (diagonalClass_restrict_fixed C c₀)

end M9Native.CurvePowerGraphFixedRestrictions

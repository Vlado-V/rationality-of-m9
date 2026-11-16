module

public import M9StacksIntegration.ChowPicardCap
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSpecField

/-!
# Genuine constant restrictions in the partition calculus

Marked vertices factor through the original field spectrum. Its actual
Picard group is zero, so these pullbacks are zero in the actual Picard
group and their actual Chern cap operators vanish on every Chow class.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerConstantClass

open CurvePowerGraphMaps CurvePowerGraphLocal CurvePowerChowFunctional

variable (k : Type u) [Field k]

theorem pullback_via_field_zero {X Y : Scheme.{u}} (g : X ⟶ Spec (.of k))
    (h : Spec (.of k) ⟶ Y) (x : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass (g ≫ h) x = 0 := by
  rw [← Stacks.Picard.schemePullbackClass_comp,
    Stacks.Picard.eq_zero_of_isField k (Stacks.Picard.schemePullbackClass h x)]
  exact map_zero (Stacks.Picard.schemePullbackClassHom g)

variable (C : Over (Spec (.of k))) (c₀ : power C 0 ⟶ C)

theorem stateMap_reindex_one_fixed (ambient : ℕ) (s : State) (i : Fin ambient)
    (hi : ∀ b ∈ s, b.testBit i.val = false) :
    stateMap C c₀ ambient s ≫ reindex C (fun _ : Fin 1 => i) =
      CartesianMonoidalCategory.toUnit (power C s.length) ≫ lift 1 (fun _ => c₀) := by
  apply Stacks.CurvePower.hom_ext 1
  intro q
  simp only [Category.assoc, reindex_coord, stateMap_coord, lift_coord]
  exact stateCoordinate_eq_fixed C c₀ s i.val hi

theorem stateMap_reindex_pair_fixed (ambient : ℕ) (s : State) (i j : Fin ambient)
    (hi : ∀ b ∈ s, b.testBit i.val = false)
    (hj : ∀ b ∈ s, b.testBit j.val = false) :
    stateMap C c₀ ambient s ≫ reindex C ![i, j] =
      CartesianMonoidalCategory.toUnit (power C s.length) ≫ lift 2 (fun _ => c₀) := by
  apply Stacks.CurvePower.hom_ext 2
  intro q
  fin_cases q
  · simp only [Category.assoc, reindex_coord, stateMap_coord, lift_coord]
    change stateCoordinate C c₀ s i.val = _
    exact stateCoordinate_eq_fixed C c₀ s i.val hi
  · simp only [Category.assoc, reindex_coord, stateMap_coord, lift_coord]
    change stateCoordinate C c₀ s j.val = _
    exact stateCoordinate_eq_fixed C c₀ s j.val hj

variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]

theorem pointClass_pullback_marked (ambient : ℕ) (s : State) (i : Fin ambient)
    (hi : ∀ b ∈ s, b.testBit i.val = false) :
    Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
      (letterClass k C c₀ ambient (.inl i)) = 0 := by
  rw [letterClass, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left,
    stateMap_reindex_one_fixed k C c₀ ambient s i hi]
  exact pullback_via_field_zero k
    (CartesianMonoidalCategory.toUnit (power C s.length)).left (lift 1 (fun _ => c₀)).left _

theorem diagonalClass_pullback_both_marked (ambient : ℕ) (s : State) (i j : Fin ambient)
    (hi : ∀ b ∈ s, b.testBit i.val = false)
    (hj : ∀ b ∈ s, b.testBit j.val = false) :
    Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
      (letterClass k C c₀ ambient (.inr (i, j))) = 0 := by
  rw [letterClass, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left,
    stateMap_reindex_pair_fixed k C c₀ ambient s i j hi hj]
  exact pullback_via_field_zero k
    (CartesianMonoidalCategory.toUnit (power C s.length)).left (lift 2 (fun _ => c₀)).left _

theorem pointCap_pullback_marked (ambient : ℕ) (s : State) (i : Fin ambient)
    (hi : ∀ b ∈ s, b.testBit i.val = false) (d : ℤ) :
    ChowPicardCap.capFun (Stacks.Chow.fieldChowSituation k) (power C s.length).hom d
      (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
        (letterClass k C c₀ ambient (.inl i))) = 0 := by
  rw [pointClass_pullback_marked k C c₀ ambient s i hi, ChowPicardCap.capFun_zero]

theorem diagonalCap_pullback_both_marked (ambient : ℕ) (s : State) (i j : Fin ambient)
    (hi : ∀ b ∈ s, b.testBit i.val = false)
    (hj : ∀ b ∈ s, b.testBit j.val = false) (d : ℤ) :
    ChowPicardCap.capFun (Stacks.Chow.fieldChowSituation k) (power C s.length).hom d
      (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left
        (letterClass k C c₀ ambient (.inr (i, j)))) = 0 := by
  rw [diagonalClass_pullback_both_marked k C c₀ ambient s i j hi hj,
    ChowPicardCap.capFun_zero]

end M9Native.CurvePowerConstantClass

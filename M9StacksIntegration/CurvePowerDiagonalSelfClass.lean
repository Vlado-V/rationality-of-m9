module

public import M9StacksIntegration.CurvePowerPointRestriction

/-!
# The literal self-diagonal line on a free partition block

When both vertices belong to the first block, the actual class is the
pullback of the original diagonal line along the repeated first
coordinate. This is a Picard-class identity; no self-intersection value
is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerDiagonalSelfClass

open CurvePowerChowFunctional CurvePowerGraphMaps

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

omit [SmoothOfRelativeDimension 1 C.hom] in
theorem isProper_power_map {m n : ℕ} (g : power C m ⟶ power C n) : IsProper g.left := by
  have h : g.left ≫ (power C n).hom = (power C m).hom := Over.w g
  have : IsProper (g.left ≫ (power C n).hom) := by
    rw [h]
    infer_instance
  exact IsProper.of_comp g.left (power C n).hom

theorem diagonalClass_pullback_same_head (ambient b : ℕ) (s : CurvePowerGraphLocal.State)
    (i j : Fin ambient) (hi : b.testBit i.val = true) (hj : b.testBit j.val = true) :
    Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient (b :: s)).left
        (letterClass k C c₀ ambient (.inr (i,j))) =
      Stacks.Picard.schemePullbackClass (CurvePowerGraphRestrictions.firstMap C s.length).left
        (Stacks.Picard.schemePullbackClass (reindex C ![(0 : Fin 1), 0]).left
          (CurvePowerGraphCartier.graphClass C 1 (coord C 1 0))) := by
  have hm : stateMap C c₀ ambient (b :: s) ≫ reindex C ![i,j] =
      CurvePowerGraphRestrictions.firstMap C s.length ≫ reindex C ![(0 : Fin 1), 0] := by
    apply Stacks.CurvePower.hom_ext 2
    intro q
    fin_cases q
    · simp only [Category.assoc, reindex_coord, stateMap_coord,
        CurvePowerGraphRestrictions.firstMap]
      exact stateCoordinate_cons_of_mem C c₀ b s i.val hi
    · simp only [Category.assoc, reindex_coord, stateMap_coord,
        CurvePowerGraphRestrictions.firstMap]
      exact stateCoordinate_cons_of_mem C c₀ b s j.val hj
  rw [letterClass, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, hm,
    Over.comp_left, ← Stacks.Picard.schemePullbackClass_comp]

end M9Native.CurvePowerDiagonalSelfClass

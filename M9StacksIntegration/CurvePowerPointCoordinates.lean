module

public import M9StacksIntegration.CurvePowerPointCapDegree
public import M9StacksIntegration.CurvePowerGraphRestrictions

/-!
# The actual point-product factors in literal coordinate notation

The recursive cap family lists the coordinate point divisors in
reverse order. This is an equality of the actual native Picard
classes, before applying a pairing or a numerical quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerPointCoordinates

open Stacks.Chow CurveTopChowClass ChowCapDegreePicard CurvePowerChowFunctional
open CurvePowerPointCapDegree

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem pointClass_pullback_second (m : ℕ) (i : Fin m) :
    Stacks.Picard.schemePullbackClass (snd C (power C m)).left
        (letterClass k C c₀ m (.inl i)) =
      letterClass k C c₀ (m + 1) (.inl i.succ) := by
  have hm : snd C (power C m) ≫ reindex C (fun _ : Fin 1 => i) =
      reindex C (fun _ : Fin 1 => i.succ) := by
    apply Stacks.CurvePower.hom_ext 1
    intro a
    simp only [Category.assoc, reindex_coord, coord_succ]
  change Stacks.Picard.schemePullbackClass (snd C (power C m)).left
    (Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => i)).left
      (CurvePowerGraphCartier.graphClass C 0 c₀)) = _
  rw [Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, hm]
  rfl

theorem pointFamily_eq_coordinate_reverse (m : ℕ) (j : Fin m) :
    pointFamily C c₀ m j = letterClass k C c₀ m (.inl (Fin.rev j)) := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
      refine Fin.lastCases ?_ (fun q => ?_) j
      · rw [pointFamily, Fin.snoc_last, Fin.rev_last]
        exact CurvePowerGraphRestrictions.constant_graphClass C c₀ m
      · rw [pointFamily, Fin.snoc_castSucc, ih q, Fin.rev_castSucc]
        exact pointClass_pullback_second k C c₀ m (Fin.rev q)

theorem capDegreePicard_reverse_points [IsAlgClosed k] [IsVariety k C.hom]
    (hC : topologicalKrullDim C.left = 1) (m : ℕ) :
    capDegreePicard k (power C m).hom
        (fun j => letterClass k C c₀ m (.inl (Fin.rev j)))
        (identityChowClass (fieldChowSituation k) (power C m).hom m) = 1 := by
  have h : (fun j => letterClass k C c₀ m (.inl (Fin.rev j))) = pointFamily C c₀ m := by
    funext j
    exact (pointFamily_eq_coordinate_reverse k C c₀ m j).symm
  rw [h]
  exact capDegreePicard_pointFamily k C c₀ hC m

end M9Native.CurvePowerPointCoordinates

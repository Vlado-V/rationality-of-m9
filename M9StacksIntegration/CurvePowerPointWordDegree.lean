module

public import M9StacksIntegration.CurvePicardWordDegree

/-! The actual point line on the actual one-fold curve power has degree
one. Consequently every projected cap word admits actual curve-degree
replacement, without a point-normalization input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.CurvePower

universe u
namespace M9Native.CurvePowerPointWordDegree

open Stacks.Chow CurveTopChowClass CurvePowerChowFunctional CurvePicardWordDegree

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

def pointClassOne : Stacks.Picard.ofScheme (power C 1).left :=
  CurvePowerGraphCartier.graphClass C 0 c₀

theorem letterClass_point_one (j : Fin 1) :
    letterClass k C c₀ 1 (.inl j) = pointClassOne k C c₀ := by
  have hj : (fun _ : Fin 1 => j) = (id : Fin 1 → Fin 1) := by
    funext a
    exact Subsingleton.elim _ _
  change Stacks.Picard.schemePullbackClass (reindex C (fun _ : Fin 1 => j)).left
    (CurvePowerGraphCartier.graphClass C 0 c₀) = _
  rw [hj, reindex_id]
  exact Stacks.Picard.schemePullbackClass_id _ _

variable [IsAlgClosed k] [IsVariety k C.hom]

theorem power_one_dim (hC : topologicalKrullDim C.left = 1) :
    topologicalKrullDim (power C 1).left = 1 := by
  rw [(isVariety_power_and_topologicalKrullDim C 1).2, hC]
  norm_num

/-- The normalization is computed from the actual point cap, not supplied. -/
theorem pointClassOne_degree (hC : topologicalKrullDim C.left = 1) :
    invertibleCurveDegreeHom k (power C 1).hom (power_one_dim k C hC).le
      (pointClassOne k C c₀) = 1 := by
  have hp := CurvePowerPointCoordinates.capDegreePicard_reverse_points k C c₀ hC 1
  have hfun : (fun j : Fin 1 => letterClass k C c₀ 1 (.inl (Fin.rev j))) =
      (fun _ : Fin 1 => pointClassOne k C c₀) := by
    funext j
    exact letterClass_point_one k C c₀ (Fin.rev j)
  rw [hfun] at hp
  have hw := CurvePowerPointTrace.wordDegree_ofFn k (power C 1).hom
    (fun _ : Fin 1 => pointClassOne k C c₀)
  have hl : List.ofFn (fun _ : Fin 1 => pointClassOne k C c₀) = [pointClassOne k C c₀] := by
    simp
  rw [hl] at hw
  rw [← picardCapDegree_identity k (power C 1).hom (power_one_dim k C hC).le]
  exact (wordDegree_singleton k (power C 1).hom (pointClassOne k C c₀)).symm.trans (hw.trans hp)

/-- Actual curve degree replaces a line by the actual point line against
every remaining cap word upstairs, retaining the original proper map. -/
theorem wordDegree_pullback_point (hC : topologicalKrullDim C.left = 1)
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (g : Y ⟶ (power C 1).left) [IsProper g]
    (hg : g ≫ (power C 1).hom = fY)
    (x : Stacks.Picard.ofScheme (power C 1).left)
    (tail : List (Stacks.Picard.ofScheme Y)) :
    wordDegree k fY ((Stacks.Picard.schemePullbackClass g x :: tail).map chosenLine) =
      invertibleCurveDegreeHom k (power C 1).hom (power_one_dim k C hC).le x *
        wordDegree k fY
          ((Stacks.Picard.schemePullbackClass g (pointClassOne k C c₀) :: tail).map chosenLine) := by
  letI : IsIntegral (power C 1).left := (isVariety_power C 1).toIsIntegral
  exact wordDegree_pullback_degree_one k (power C 1).hom (power_one_dim k C hC)
    x (pointClassOne k C c₀) (pointClassOne_degree k C c₀ hC) fY g hg tail

end M9Native.CurvePowerPointWordDegree

module

public import M9StacksIntegration.DirectC9NormalizationClass

/-!
# The literal moving-graph quotient lines and their actual Picard classes

The j-th line is the actual restriction of the j+1-st actual partial
family line to the j-th moving section. Its actual integral Picard class
is minus the point sum plus seventeen point classes and ALL j+1 graph
intersections, including its actual self-diagonal class. No numerical
replacement of that self-line, Chern formula or assumed filtration is
used here; the actual ordinary short exact rows are a separate step.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.DirectC9MovingQuotientClass

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection familyClass)
open DirectC9NormalizationClass
open PoincareChern (lineClass)

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

abbrev movingSection (i : Fin 9) : (power C 9).left ⟶ familySpace C :=
  Stacks.Hilbert.pointGraph C (power C 9) (coord C 9 i)

@[simp] theorem movingSection_comp_projection (i : Fin 9) :
    movingSection C i ≫ familyProjection C = 𝟙 _ :=
  Stacks.Hilbert.pointGraph_comp_snd C (power C 9) (coord C 9 i)

abbrev diagonalClassAt (i a : Fin 9) : Stacks.Picard.ofScheme (power C 9).left :=
  Stacks.Picard.schemePullbackClass (reindex C ![i,a]).left
    (CurvePowerGraphRestrictions.diagonalClass C)

/-- The literal actual line on the moving point, with its actual self-intersection retained. -/
abbrev movingQuotientLine (j : ℕ) (hj : j + 1 ≤ 9) : (power C 9).left.Modules :=
  (Scheme.Modules.pullback (movingSection C ⟨j,by omega⟩)).obj
    (partialLine C c₀ (j + 1) hj)

instance movingQuotientLine_isInvertible (j : ℕ) (hj : j + 1 ≤ 9) :
    Stacks.SheafOfModules.IsInvertible (power C 9).left.presheaf (power C 9).left.ringCatSheaf.2
      (movingQuotientLine C c₀ j hj) := by
  letI := partialLine_isInvertible C c₀ (j + 1) hj
  exact Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj
    (movingSection C ⟨j,by omega⟩) (partialLine C c₀ (j + 1) hj)

/-- The exact actual Picard formula needed by the genuine operational Whitney computation. -/
theorem movingQuotientLine_class (j : ℕ) (hj : j + 1 ≤ 9) :
    @lineClass (power C 9).left (movingQuotientLine C c₀ j hj)
      (movingQuotientLine_isInvertible C c₀ j hj) =
      -pointSum C c₀ + 17 • pointClassAt C c₀ ⟨j,by omega⟩ +
        ∑ a : Fin (j + 1), diagonalClassAt C ⟨j,by omega⟩ ⟨a.val,by omega⟩ := by
  let s := movingSection C ⟨j,by omega⟩
  let H := Stacks.Picard.schemePullbackClassHom s
  let nc := @lineClass (power C 9).left (inverseNormalizationLine C c₀)
    (DirectC9FamilyDegree.inverseNormalizationLine_isInvertible C c₀)
  have hb : H (Stacks.Picard.schemePullbackClass (familyProjection C) nc) = nc := by
    change Stacks.Picard.schemePullbackClass s (Stacks.Picard.schemePullbackClass (familyProjection C) nc) = nc
    rw [Stacks.Picard.schemePullbackClass_comp,movingSection_comp_projection C ⟨j,by omega⟩,Stacks.Picard.schemePullbackClass_id]
  have hf : H (graphFamilyClass C (constantPoint C c₀)) = pointClassAt C c₀ ⟨j,by omega⟩ :=
    CurvePowerGraphRestrictions.constant_graphClass_restrict_coordinate C c₀ 9 ⟨j,by omega⟩
  have hm : H (movingClassSum C (j + 1) hj) =
      ∑ a : Fin (j + 1), diagonalClassAt C ⟨j,by omega⟩ ⟨a.val,by omega⟩ := by
    change H (∑ a : Fin (j + 1), graphFamilyClass C (coord C 9 ⟨a.val,by omega⟩)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact CurvePowerGraphRestrictions.coordinate_graphClass_restrict_coordinate C 9
      ⟨j,by omega⟩ ⟨a.val,by omega⟩
  have hd : H (familyClass C (partialFamily C c₀ (j + 1) hj)) =
      17 • pointClassAt C c₀ ⟨j,by omega⟩ +
        ∑ a : Fin (j + 1), diagonalClassAt C ⟨j,by omega⟩ ⟨a.val,by omega⟩ := by
    rw [partialFamily_class,map_add,map_nsmul,hf,hm]
  have hp := @PoincareChern.lineClass_pullback (power C 9).left (familySpace C) s
    (partialLine C c₀ (j + 1) hj) (partialLine_isInvertible C c₀ (j + 1) hj)
  have hu := congrArg H (DirectC9FamilyDegree.partialLine_class C c₀ (j + 1) hj)
  have hx := (hp.trans hu).trans ((map_add H _ _).trans
    (congrArg₂ (fun x y : Stacks.Picard.ofScheme (power C 9).left => x + y) hb hd))
  have hnc : nc = -pointSum C c₀ := inverseNormalizationLine_class C c₀
  exact hx.trans (by rw [hnc]; exact (add_assoc _ _ _).symm)

end M9Native.DirectC9MovingQuotientClass

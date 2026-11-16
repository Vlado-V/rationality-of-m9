module

public import M9StacksIntegration.PencilDegreePullback
public import StacksFrontier.AlgebraicGeometry.Curves.FlatMorphism
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# The actual finite-flat rank of a nonconstant proper curve map

This is the selected finite-flat-rank argument from the pinned native
`Curves/SeparableClosedPoint.lean`, theorem
`isFiniteLocallyFreeOfRank_degreeOver_of_not_constant`. Only its ready
flatness, finite-flat, and actual generic pushforward rank parents are
used. The broad Frobenius and inseparable-point developments are not
needed for this theorem. Native source copyright and Apache-2.0 license
are retained in the audit provenance.

Finiteness, flatness, and the rank are all derived from the original
nonconstant map. No finite-flat or fibre-rank premise is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.CurveMapFiniteFlatDegree

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
  [IsCurve K fX] [IsCurve K fY] [IsProper fX] [IsProper fY] [IsNormal Y]

/-- The genuine finite-flat rank is the original function-field degree. -/
theorem finiteLocallyFreeOfRank_curveMapDegree (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank g
      (PencilDegreePullback.curveMapDegree fX fY g hg hnc) := by
  let : IsFinite g := isFinite_of_not_constant K fX fY g hg hnc
  have hrange : (Set.range g).Nontrivial := by
    by_contra h
    rw [Set.not_nontrivial_iff] at h
    exact hnc ⟨g.base (genericPoint X), fun x => h ⟨x,rfl⟩ ⟨_,rfl⟩⟩
  let : Flat g :=
    (Flat.iff_flat_stalkMap g).2 (isFlat_of_nonconstant_of_isNormal fX fY g hg hrange)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree g :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian g).2
      ⟨inferInstance,inferInstance⟩
  let := hflf.toIsFiniteLocallyFree
  exact (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff g _).2 ⟨inferInstance,
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq _ _ (genericPoint Y)
      (fiberRank_pushforward_unit_genericPoint_eq_degreeOver K fX fY g hg hnc)⟩

end M9Native.CurveMapFiniteFlatDegree

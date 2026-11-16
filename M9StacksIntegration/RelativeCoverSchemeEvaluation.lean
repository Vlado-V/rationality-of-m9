module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismHom
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Original scheme evaluation of an actual native relative morphism

When the original source and target are represented schemes, native
relative-Hom evaluation is read by fully faithful Yoneda. The chosen
representing source has the genuine original cartesian source-family
square, and its evaluation retains the same original base projection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

namespace M9Native.RelativeCoverSchemeEvaluation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z X Q Y : BigFppfOver B S hS} (z : Z ⟶ Q) (x : X ⟶ Q)
  (p : RelativeMorphism B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
    (yoneda.map z) (yoneda.map x) (yoneda.obj Y))
  (hz : yoneda.relativelyRepresentable (yoneda.map z))

/-- The actual scheme representing the pulled original source family. -/
abbrev source : BigFppfOver B S hS := hz.pullback p.base

/-- Its original projection to the parameter scheme. -/
abbrev projection : source z x p hz ⟶ Y := hz.snd p.base

/-- Its original map to the original source scheme. -/
def toOriginal : source z x p hz ⟶ Z := yoneda.preimage (hz.fst p.base)

/-- The original parameter map read from the native relative morphism. -/
def base : Y ⟶ Q := yoneda.preimage p.base

/-- The genuine native universal evaluation on the chosen source model. -/
def nativeEvaluation : yoneda.obj (source z x p hz) ⟶ yoneda.obj X :=
  (hz.isPullback p.base).flip.isoPullback.hom ≫ p.morphism

/-- The SAME native evaluation, now as an original scheme-site map. -/
def evaluation : source z x p hz ⟶ X := yoneda.preimage (nativeEvaluation z x p hz)

/-- The original site square is cartesian; no source isomorphism is assumed. -/
theorem sourceSquare :
    IsPullback (toOriginal z x p hz) (projection z x p hz) z (base z x p) := by
  apply IsPullback.of_map_of_faithful yoneda
  simpa only [toOriginal, projection, base, Functor.map_preimage] using hz.isPullback p.base

/-- The actual evaluation commutes with the actual original base maps. -/
theorem evaluation_over :
    evaluation z x p hz ≫ x = projection z x p hz ≫ base z x p := by
  apply yoneda.map_injective
  simp only [Functor.map_comp, evaluation, base, Functor.map_preimage]
  change ((hz.isPullback p.base).flip.isoPullback.hom ≫ p.morphism) ≫ yoneda.map x =
    yoneda.map (hz.snd p.base) ≫ p.base
  rw [Category.assoc, p.commutes, ← Category.assoc,
    (hz.isPullback p.base).flip.isoPullback_hom_snd]
  exact (hz.isPullback p.base).w

/-- Reading the actual site square on schemes gives the literal original
cartesian curve-family square, including nonreduced parameter schemes. -/
theorem originalSourceSquare :
    IsPullback ((BigFppfOver.toScheme B S hS).map (toOriginal z x p hz))
      ((BigFppfOver.toScheme B S hS).map (projection z x p hz))
      ((BigFppfOver.toScheme B S hS).map z)
      ((BigFppfOver.toScheme B S hS).map (base z x p)) :=
  (sourceSquare z x p hz).map (BigFppfOver.toScheme B S hS)

/-- The original scheme evaluation retains the actual original ground square. -/
theorem originalEvaluation_over :
    (BigFppfOver.toScheme B S hS).map (evaluation z x p hz) ≫
      (BigFppfOver.toScheme B S hS).map x =
    (BigFppfOver.toScheme B S hS).map (projection z x p hz) ≫
      (BigFppfOver.toScheme B S hS).map (base z x p) := by
  rw [← Functor.map_comp, evaluation_over, Functor.map_comp]

/-- Properness of the actual original source family descends to the
actual universal evaluation source by its genuine pullback square. -/
theorem originalProjection_isProper
    [IsProper ((BigFppfOver.toScheme B S hS).map z)] :
    IsProper ((BigFppfOver.toScheme B S hS).map (projection z x p hz)) :=
  MorphismProperty.of_isPullback (P := @IsProper) (originalSourceSquare z x p hz) inferInstance

/-- The actual universal cover source is a smooth relative curve when
the original polarized equation family is one. -/
theorem originalProjection_isSmoothRelativeCurve
    [SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B S hS).map z)] :
    SmoothOfRelativeDimension 1
      ((BigFppfOver.toScheme B S hS).map (projection z x p hz)) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (originalSourceSquare z x p hz) inferInstance

end M9Native.RelativeCoverSchemeEvaluation
end

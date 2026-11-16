module

public import M9StacksIntegration.GenusNineSourceOpen
public import M9StacksIntegration.PolarizedCurveDegreeOpen
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase

/-!
# Actual degree-forty-eight smooth genus-nine equation models

First restrict a genuine flat proper equation model to its actual smooth
genus-nine open. Then restrict the actual embedding line to the actual
open-and-closed degree-forty-eight locus. Every original smooth genus-nine
curve whose actual embedding line has degree forty-eight lifts through
both restrictions, retaining its original cartesian square.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.GenusNinePolarizedSourceOpen

variable {X T : Scheme.{u}} (p : X ⟶ T)
  [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
  (N : X.Modules)
  [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]

abbrev firstLine (U : T.Opens) : (p ⁻¹ᵁ U).toScheme.Modules :=
  (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj N

theorem firstLine_stacksInvertible (U : T.Opens) :
    Stacks.SheafOfModules.IsInvertible (p ⁻¹ᵁ U).toScheme.presheaf
      (p ⁻¹ᵁ U).toScheme.ringCatSheaf.2 (firstLine p N U) :=
  Stacks.RingedSpace.modulePullback_isInvertible_of (p ⁻¹ᵁ U).ι.toLRSHom.toShHom N (PolarizedCurveDegreeOpen.stacksInvertible N)

abbrev boundedOpen (U : T.Opens) : U.toScheme.Opens :=
  PolarizedCurveDegreeOpen.degreeOpen (p ∣_ U) (firstLine p N U) 48

abbrev projection (U : T.Opens) := (p ∣_ U) ∣_ boundedOpen p N U

abbrev line (U : T.Opens) :
    ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).toScheme.Modules :=
  (Scheme.Modules.pullback ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).ι).obj (firstLine p N U)

local instance lineInvertible (U : T.Opens) :
    SheafOfModules.IsInvertible ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).toScheme.presheaf
      ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).toScheme.ringCatSheaf.2 (line p N U) := by
  dsimp only [line, firstLine]
  infer_instance

abbrev baseMap (U : T.Opens) : (boundedOpen p N U).toScheme ⟶ T :=
  (boundedOpen p N U).ι ≫ U.ι

abbrev totalMap (U : T.Opens) :
    ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).toScheme ⟶ X :=
  ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).ι ≫ (p ⁻¹ᵁ U).ι

/-- Both open restrictions are genuine pullbacks of the original family. -/
theorem originalSquare (U : T.Opens) :
    IsPullback (totalMap p N U) (projection p N U) p (baseMap p N U) :=
  (isPullback_morphismRestrict (p ∣_ U) (boundedOpen p N U)).flip.paste_horiz
    (isPullback_morphismRestrict p U).flip

/-- The literal original relative polarization stays ample after both
actual open restrictions. -/
theorem line_isRelativelyAmple (U : T.Opens)
    (ha : Stacks.RelativeAmple.IsRelativelyAmple p N) :
    Stacks.RelativeAmple.IsRelativelyAmple (projection p N U) (line p N U) :=
  Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_morphismRestrict
    (p ∣_ U) (firstLine p N U)
    (Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_morphismRestrict p N ha U)
    (boundedOpen p N U)

/-- Genuine finite-type geometry of the actual nested parameter open. -/
theorem baseMap_finiteType [IsNoetherian T] {A : Scheme.{u}}
    (s : T ⟶ A) [LocallyOfFiniteType s] (U : T.Opens) :
    LocallyOfFiniteType (baseMap p N U ≫ s) ∧
      QuasiCompact (baseMap p N U ≫ s) := by
  refine ⟨inferInstance, ?_⟩
  infer_instance

/-- The construction gives actual relative curves with actual line degree
forty-eight on all ORIGINAL field fibres and covers every original
polarized smooth proper genus-nine fibre of the equation model. -/
theorem exists_polarizedSourceOpen [IsNoetherian T] :
    ∃ U : T.Opens, SmoothOfRelativeDimension 1 (projection p N U) ∧
      (∀ (K : Type u) [Field K] (V : Scheme.{u})
        (y : Spec (.of K) ⟶ boundedOpen p N U)
        (q : V ⟶ ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U)) (f : V ⟶ Spec (.of K))
        [IsProper f], IsPullback q f (projection p N U) y →
          IsCurve K f ∧ IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) ∧ genus f = 9 ∧
            ∀ hdim : topologicalKrullDim V ≤ 1,
              invertibleCurveDegree K f hdim ((Scheme.Modules.pullback q).obj (line p N U)) = 48) ∧
      (∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ T)
        (q : V ⟶ X) (f : V ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
        [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (_ : genus f = 9)
        (hd : invertibleCurveDegree K f
          (IsCurve.topologicalKrullDim_eq_one (f := f)).le ((Scheme.Modules.pullback q).obj N) = 48),
        IsPullback q f p y →
          ∃ (y' : Spec (.of K) ⟶ boundedOpen p N U)
            (q' : V ⟶ ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U)),
            y' ≫ baseMap p N U = y ∧ q' ≫ totalMap p N U = q ∧
              IsPullback q' f (projection p N U) y') := by
  obtain ⟨U, hsm, hgeom, hcov⟩ := GenusNineSourceOpen.exists_sourceOpen_covering_original_curves p
  have : SmoothOfRelativeDimension 1 (p ∣_ U) := hsm
  have hsm' : SmoothOfRelativeDimension 1 (projection p N U) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (isPullback_morphismRestrict (p ∣_ U) (boundedOpen p N U)).flip hsm
  refine ⟨U, hsm', ?_, ?_⟩
  · intro K _ V y q f _ sq
    have hbig := sq.paste_horiz
      (isPullback_morphismRestrict (p ∣_ U) (boundedOpen p N U)).flip
    have h := hgeom K V (y ≫ (boundedOpen p N U).ι)
      (q ≫ ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).ι) f hbig
    refine ⟨h.1, h.2.2.1, h.2.2.2, fun hd => ?_⟩
    exact PolarizedCurveDegreeOpen.restricted_fieldDegree (p ∣_ U) (firstLine p N U)
      48 hd sq
  · intro K _ V y q f _ _ _ _ hg hd sq
    obtain ⟨y₁,q₁,hy₁,hq₁,sq₁⟩ := hcov K V y q f hg sq
    let eN : (Scheme.Modules.pullback q₁).obj (firstLine p N U) ≅
        (Scheme.Modules.pullback q).obj N :=
      (Scheme.Modules.pullbackComp q₁ (p ⁻¹ᵁ U).ι).app N ≪≫
        (Scheme.Modules.pullbackCongr hq₁).app N
    have hd₁ : invertibleCurveDegree K f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        ((Scheme.Modules.pullback q₁).obj (firstLine p N U)) = 48 :=
      (invertibleCurveDegree_eq_of_iso K f _ eN).trans hd
    obtain ⟨y₂,q₂,hy₂,hq₂,sq₂⟩ := PolarizedCurveDegreeOpen.exists_lift_of_degree
      (p ∣_ U) (firstLine p N U)
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le sq₁ 48 hd₁
    refine ⟨y₂,q₂,?_,?_,sq₂⟩
    · change y₂ ≫ (boundedOpen p N U).ι ≫ U.ι = y
      rw [← Category.assoc, hy₂, hy₁]
    · change q₂ ≫ ((p ∣_ U) ⁻¹ᵁ boundedOpen p N U).ι ≫ (p ⁻¹ᵁ U).ι = q
      rw [← Category.assoc, hq₂, hq₁]

end M9Native.GenusNinePolarizedSourceOpen
end

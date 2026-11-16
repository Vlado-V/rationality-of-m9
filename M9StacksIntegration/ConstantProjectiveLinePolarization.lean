module

public import M9StacksIntegration.ConstantProjectiveLineFibre
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.VeryAmple
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MonomialSectionTransport
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange

/-! The genuine hyperplane line on the original constant projective line.
The original pullback square and every original field map are retained.
The degree calculation uses the canonical twisting-sheaf comparison with
the polynomial model, rather than a chosen degree-one line. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

universe u

namespace M9Native.ConstantProjectiveLinePolarization

open PencilProjectiveLineGeometry
attribute [local instance] isCurve_projectiveSpaceOver_one
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

/-- The true relative `O(1)`, pulled from the integral projective line. -/
abbrev groundLine : (Line K).Modules :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver 1 (Spec (.of K)) 1

instance groundLine_isInvertible :
    SheafOfModules.IsInvertible (Line K).presheaf (Line K).ringCatSheaf.2 (groundLine K) :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver 1 _ 1

/-- Every actual coefficient map carries the true hyperplane line to the
true hyperplane line. No algebra structure or compatibility is supplied. -/
def groundLinePullbackIso (L : Type u) [Field L]
    (h : Spec (.of L) ⟶ Spec (.of K)) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap 1 h)).obj (groundLine K) ≅
      groundLine L :=
  Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso 1 h 1

/-- Identity immersion into the actual relative projective line supplies
very ampleness of its genuine `O(1)`. -/
theorem groundLine_isRelativelyVeryAmple :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (toBase K) (groundLine K) := by
  exact Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion 1
    (toBase K) (groundLine K) (𝟙 (Line K)) inferInstance (Category.id_comp _)
    ((Scheme.Modules.pullbackId (Line K)).app (groundLine K)).symm

theorem groundLine_isRelativelyAmple :
    Stacks.RelativeAmple.IsRelativelyAmple (toBase K) (groundLine K) :=
  Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple _ _ inferInstance
    (groundLine_isRelativelyVeryAmple K)

/-- Degree transport along a genuine scheme isomorphism, with the
literal field structure map and inverse image of the original module. -/
theorem invertibleCurveDegree_pullback_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (p : Y ⟶ Spec (.of K)) [IsProper p] [IsProper (e.hom ≫ p)]
    (hX : topologicalKrullDim X ≤ 1) (hY : topologicalKrullDim Y ≤ 1)
    (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] :
    invertibleCurveDegree K (e.hom ≫ p) hX ((Scheme.Modules.pullback e.hom).obj M) =
      invertibleCurveDegree K p hY M := by
  unfold invertibleCurveDegree
  simp only [finrank_cohomologyOverField_pullback K e.hom p M,
    finrank_cohomologyOverField_unit_pushforward K e.hom p]

/-- The true `O(1)` on the original relative model has degree one. -/
theorem groundLine_degree :
    invertibleCurveDegree K (toBase K) (lineDimension K) (groundLine K) = 1 := by
  let : IsProper (projToSpecCoeff K 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff K 1
  let e := Stacks.ProjectiveCohomology.projModelIso K 1
  have hb : e.hom ≫ toBase K = projToSpecCoeff K 1 :=
    (Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism K 1).trans
      (Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec K 1).symm
  let hd := (Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin K (r := 2) two_pos).le
  have h := invertibleCurveDegree_pullback_iso K e (toBase K) hd (lineDimension K)
    (groundLine K)
  simp only [hb] at h
  calc
    invertibleCurveDegree K (toBase K) (lineDimension K) (groundLine K) =
        invertibleCurveDegree K (projToSpecCoeff K 1) hd
          ((Scheme.Modules.pullback e.hom).obj (groundLine K)) := h.symm
    _ = invertibleCurveDegree K (projToSpecCoeff K 1) hd
          (ProjectiveSpectrum.Proj.twistingSheafModule
            (Stacks.ProjectiveCohomology.polyGrading K 1) 1) :=
      invertibleCurveDegree_eq_of_iso K (projToSpecCoeff K 1) hd
        (Stacks.ProjectiveCohomology.canonicalPullbackProjModelIsoHomTwistOverIso K 1 1)
    _ = 1 := invertibleCurveDegree_twistingSheaf_one

theorem groundLinePullback_degree (L : Type u) [Field L]
    (h : Spec (.of L) ⟶ Spec (.of K)) :
    invertibleCurveDegree L (toBase L) (lineDimension L)
      ((Scheme.Modules.pullback (projectiveSpaceOverMap 1 h)).obj (groundLine K)) = 1 :=
  (invertibleCurveDegree_eq_of_iso L (toBase L) (lineDimension L)
    (groundLinePullbackIso K L h)).trans (groundLine_degree L)

variable {T : Scheme.{u}} (s : T ⟶ Spec (.of K))

/-- The literal original constant family. -/
abbrev target : Scheme.{u} := ConstantProjectiveLineFibre.target K s
abbrev projection : target K s ⟶ T := ConstantProjectiveLineFibre.projection K s
abbrev toGroundLine : target K s ⟶ Line K := pullback.fst (toBase K) s

theorem originalSquare : IsPullback (toGroundLine K s) (projection K s) (toBase K) s :=
  IsPullback.of_hasPullback (toBase K) s

instance projection_isProper : IsProper (projection K s) := by
  let : IsProper (toBase K) := inferInstance
  change IsProper (pullback.snd (toBase K) s)
  infer_instance
instance projection_isLocallyOfFinitePresentation :
    LocallyOfFinitePresentation (projection K s) := by
  let : LocallyOfFinitePresentation (toBase K) := inferInstance
  change LocallyOfFinitePresentation (pullback.snd (toBase K) s)
  infer_instance
instance projection_isSmoothRelativeCurve : SmoothOfRelativeDimension 1 (projection K s) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (originalSquare K s) inferInstance
instance projection_isFlat : Flat (projection K s) := by
  let : Flat (toBase K) := inferInstance
  change Flat (pullback.snd (toBase K) s)
  infer_instance

/-- The constant target is in the same native bound as its actual base. -/
theorem target_contains (B : BigFppfSite.{u}) (hT : B.Contains T) :
    B.Contains (target K s) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (projection K s) hT

/-- The original target line is exactly the inverse image of true `O(1)`. -/
abbrev targetLine : (target K s).Modules :=
  (Scheme.Modules.pullback (toGroundLine K s)).obj (groundLine K)

instance targetLine_isInvertible : SheafOfModules.IsInvertible (target K s).presheaf
    (target K s).ringCatSheaf.2 (targetLine K s) := inferInstance

theorem targetLine_isRelativelyVeryAmple [IsAffine T] :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (projection K s) (targetLine K s) :=
  isRelativelyVeryAmple_baseChange (originalSquare K s) (groundLine K)
    (groundLine_isRelativelyVeryAmple K)

/-- Relative ampleness follows for every original base, including the
actual affine model base, along the genuine cartesian square. -/
theorem targetLine_isRelativelyAmple :
    Stacks.RelativeAmple.IsRelativelyAmple (projection K s) (targetLine K s) :=
  Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback
    (originalSquare K s) (groundLine K) (groundLine_isRelativelyAmple K)

variable (L : Type u) [Field L] {W : Scheme.{u}}
  (a : Spec (.of L) ⟶ T) (r : W ⟶ target K s) (f : W ⟶ Spec (.of L))
  (sq : IsPullback r f (projection K s) a)

/-- An arbitrary actual original field square is physically the literal
native line over that field. -/
def originalFieldIso : W ≅ Line L :=
  (sq.paste_horiz (originalSquare K s)).isoIsPullback _ _
    (isPullback_projectiveSpaceOverMap 1 (a ≫ s))

theorem originalFieldIso_over : (originalFieldIso K s L a r f sq).hom ≫ toBase L = f :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

theorem originalFieldIso_toOriginal :
    (originalFieldIso K s L a r f sq).hom ≫ projectiveSpaceOverMap 1 (a ≫ s) =
      r ≫ toGroundLine K s :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

include sq in
theorem originalField_geometry :
    IsProper f ∧ LocallyOfFinitePresentation f ∧ SmoothOfRelativeDimension 1 f ∧ Flat f :=
  ⟨MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq inferInstance,
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq inferInstance,
    MorphismProperty.of_isPullback (P := @Flat) sq inferInstance⟩

include sq in
theorem originalField_dimension : topologicalKrullDim W ≤ 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (originalFieldIso K s L a r f sq).hom.homeomorph.isHomeomorph).le.trans (lineDimension L)

/-- The physical field comparison identifies the actual original target
line with the true hyperplane line over the actual field. -/
def originalFieldLineIso :
    (Scheme.Modules.pullback r).obj (targetLine K s) ≅
      (Scheme.Modules.pullback (originalFieldIso K s L a r f sq).hom).obj (groundLine L) :=
  (Scheme.Modules.pullbackComp r (toGroundLine K s)).app (groundLine K) ≪≫
    (Scheme.Modules.pullbackCongr (originalFieldIso_toOriginal K s L a r f sq).symm).app
      (groundLine K) ≪≫
    ((Scheme.Modules.pullbackComp (originalFieldIso K s L a r f sq).hom
      (projectiveSpaceOverMap 1 (a ≫ s))).app (groundLine K)).symm ≪≫
    (Scheme.Modules.pullback (originalFieldIso K s L a r f sq).hom).mapIso
      (groundLinePullbackIso K L (a ≫ s))

include sq in
theorem originalFieldLine_degree [IsProper f] (hd : topologicalKrullDim W ≤ 1) :
    invertibleCurveDegree L f hd ((Scheme.Modules.pullback r).obj (targetLine K s)) = 1 := by
  let e := originalFieldIso K s L a r f sq
  have he : e.hom ≫ toBase L = f := originalFieldIso_over K s L a r f sq
  have hi := invertibleCurveDegree_pullback_iso L e (toBase L) hd (lineDimension L)
    (groundLine L)
  simp only [he] at hi
  exact (invertibleCurveDegree_eq_of_iso L f hd
    (originalFieldLineIso K s L a r f sq)).trans (hi.trans (groundLine_degree L))

/-- Every original field reading has degree one; its properness and
dimension are derived from its genuine field square. -/
theorem originalFieldDegree_eq_one :
    letI := (originalField_geometry K s L a r f sq).1
    invertibleCurveDegree L f (originalField_dimension K s L a r f sq)
      ((Scheme.Modules.pullback r).obj (targetLine K s)) = 1 := by
  let : IsProper f := (originalField_geometry K s L a r f sq).1
  exact originalFieldLine_degree K s L a r f sq (originalField_dimension K s L a r f sq)

/-- The literal field fibre's pulled target line. -/
abbrev fieldLine (i : Spec (.of L) ⟶ T) :
    (ConstantProjectiveLineFibre.fieldFibre K L s i).Modules :=
  (Scheme.Modules.pullback (pullback.fst (projection K s) i)).obj (targetLine K s)

def fieldLineIso (i : Spec (.of L) ⟶ T) :
    fieldLine K s L i ≅
      (Scheme.Modules.pullback (ConstantProjectiveLineFibre.fibreIso K L s i).hom).obj
        (groundLine L) :=
  originalFieldLineIso K s L i _ _ (IsPullback.of_hasPullback (projection K s) i)

/-- The original reading transported onto the literal line over `L`. -/
abbrev readingLine (i : Spec (.of L) ⟶ T) : (Line L).Modules :=
  (Scheme.Modules.pullback (ConstantProjectiveLineFibre.fibreIso K L s i).inv).obj
    (fieldLine K s L i)

instance readingLine_isInvertible (i : Spec (.of L) ⟶ T) :
    SheafOfModules.IsInvertible (Line L).presheaf (Line L).ringCatSheaf.2
      (readingLine K s L i) := inferInstance

def readingLineIso (i : Spec (.of L) ⟶ T) : readingLine K s L i ≅ groundLine L :=
  (Scheme.Modules.pullback (ConstantProjectiveLineFibre.fibreIso K L s i).inv).mapIso
      (fieldLineIso K s L i) ≪≫
    (Scheme.Modules.pullbackComp (ConstantProjectiveLineFibre.fibreIso K L s i).inv
      (ConstantProjectiveLineFibre.fibreIso K L s i).hom).app (groundLine L) ≪≫
    (Scheme.Modules.pullbackCongr
      (ConstantProjectiveLineFibre.fibreIso K L s i).inv_hom_id).app (groundLine L) ≪≫
    (Scheme.Modules.pullbackId (Line L)).app (groundLine L)

theorem readingLine_degree (i : Spec (.of L) ⟶ T) :
    invertibleCurveDegree L (toBase L) (lineDimension L) (readingLine K s L i) = 1 :=
  (invertibleCurveDegree_eq_of_iso L (toBase L) (lineDimension L)
    (readingLineIso K s L i)).trans (groundLine_degree L)

end M9Native.ConstantProjectiveLinePolarization
end

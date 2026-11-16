module

public import M9StacksIntegration.GenusNineBoundedPolarizedModels
public import M9StacksIntegration.PolarizedCurveGroundFieldBaseChange

/-! Actual finite affine polarized source models over the chosen ground field.
Every source is the literal original base change of a constructed finite
integer equation model. Its line, original projective embedding triangle,
and coverage of every original algebraically closed extension are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace M9Native.GenusNineGroundFieldPolarizedModels

/-- This records an actual constructed affine equation model. All ground
field family geometry below is derived from its literal base change. -/
structure Model (K : Type u) [Field K] (m : ℕ) where
  original : GenusNineBoundedPolarizedModels.Family.{u} m
  affine : IsAffine original.parameter

attribute [instance] Model.affine

namespace Model

variable {K : Type u} [Field K] {m : ℕ} (D : Model.{u} K m)

abbrev integerStructure := D.original.coefficientMap ≫
  GenusNineBoundedPolarizedModels.coefficientToInteger.{u} m

instance integerFinitePresentation : LocallyOfFinitePresentation D.integerStructure :=
  D.original.parameterFinitePresentation
instance integerQuasiCompact : QuasiCompact D.integerStructure :=
  D.original.parameterQuasiCompact

abbrev parameter : Scheme.{u} := PolarizedCurveGroundFieldBaseChange.parameter D.integerStructure K
abbrev parameterMap : D.parameter ⟶ D.original.parameter :=
  PolarizedCurveGroundFieldBaseChange.parameterMap D.integerStructure K
abbrev structureMap : D.parameter ⟶ Spec (.of K) :=
  PolarizedCurveGroundFieldBaseChange.structureMap D.integerStructure K
abbrev total : Scheme.{u} :=
  PolarizedCurveGroundFieldBaseChange.total D.original.projection D.integerStructure K
abbrev totalMap : D.total ⟶ D.original.total :=
  PolarizedCurveGroundFieldBaseChange.totalMap D.original.projection D.integerStructure K
abbrev projection : D.total ⟶ D.parameter :=
  PolarizedCurveGroundFieldBaseChange.projection D.original.projection D.integerStructure K
abbrev line : D.total.Modules :=
  PolarizedCurveGroundFieldBaseChange.line D.original.projection D.integerStructure K D.original.line

instance parameterAffine : IsAffine D.parameter := inferInstance
instance parameterFinitePresentation : LocallyOfFinitePresentation D.structureMap := inferInstance
instance parameterQuasiCompact : QuasiCompact D.structureMap := inferInstance

instance parameterNoetherian : IsNoetherian D.parameter := by
  letI : IsLocallyNoetherian D.parameter := LocallyOfFiniteType.isLocallyNoetherian D.structureMap
  exact ⟨⟩

instance projectionProper : IsProper D.projection := inferInstance
instance projectionSmooth : SmoothOfRelativeDimension 1 D.projection := inferInstance
instance lineInvertible : SheafOfModules.IsInvertible D.total.presheaf D.total.ringCatSheaf.2 D.line :=
  inferInstance

/-- The original source square is the actual categorical base change. -/
theorem originalSquare : IsPullback D.totalMap D.projection D.original.projection D.parameterMap :=
  PolarizedCurveGroundFieldBaseChange.originalSquare D.original.projection D.integerStructure K

/-- The actual original family is a curve over every original field point. -/
theorem schemeCurve : M9StandaloneDraft.SchemeCurve D.projection 9 :=
  PolarizedCurveGroundFieldBaseChange.schemeCurve D.original.projection D.integerStructure K
    D.original.schemeCurve

/-- The original equation polarization remains relatively ample. -/
theorem relativelyAmple : Stacks.RelativeAmple.IsRelativelyAmple D.projection D.line :=
  PolarizedCurveGroundFieldBaseChange.line_isRelativelyAmple D.original.projection D.integerStructure K
    D.original.line D.original.relativelyAmple

abbrev coefficientMap : D.parameter ⟶ Spec (.of (GenusNineFiniteEquationFamilies.coefficientRing.{u} m)) :=
  D.parameterMap ≫ D.original.coefficientMap
abbrev ambientMap : D.total ⟶
    projectiveSpaceOverRing 39 (.of (GenusNineFiniteEquationFamilies.coefficientRing.{u} m)) :=
  D.totalMap ≫ D.original.ambientMap

/-- All true source geometry and degree forty-eight hold over every
original field, not only native-contained or algebraically closed fields. -/
theorem fieldGeometry (L : Type u) [Field L] (V : Scheme.{u})
    (a : Spec (.of L) ⟶ D.parameter) (q : V ⟶ D.total) (f : V ⟶ Spec (.of L))
    [IsProper f] (sq : IsPullback q f D.projection a) :
    IsCurve L f ∧ IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ f.appTop) ∧ genus f = 9 ∧
      ∀ hd : topologicalKrullDim V ≤ 1,
        invertibleCurveDegree L f hd ((Scheme.Modules.pullback q).obj D.line) = 48 := by
  have h := D.original.fieldGeometry L V (a ≫ D.parameterMap) (q ≫ D.totalMap) f
    (sq.paste_horiz D.originalSquare)
  refine ⟨h.1,h.2.1,h.2.2.1,fun hd => ?_⟩
  exact (invertibleCurveDegree_eq_of_iso L f hd
    (PolarizedCurveGroundFieldBaseChange.fieldLineIso D.original.projection D.integerStructure K
      D.original.line q)).trans (h.2.2.2 hd)

/-- Native containment of the actual affine ground parameter is derived
from its true finite-type ground structure. -/
theorem parameter_contains (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))) :
    B.Contains D.parameter :=
  PolarizedCurveGroundFieldBaseChange.parameter_contains D.integerStructure K B hK

/-- Native source containment is derived from the actual proper projection. -/
theorem total_contains (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))) :
    B.Contains D.total :=
  PolarizedCurveGroundFieldBaseChange.total_contains D.original.projection D.integerStructure K B hK

end Model

/-- Finitely many actual affine source families over the chosen ground
field cover every original algebraically closed extension curve. The
literal projective embedding and tricanonical line are retained. -/
theorem exists_finite_models (K : Type u) [Field K] :
    ∃ (m t : ℕ) (n : Fin t → ℕ) (D : (Σ i : Fin t, Fin (n i)) → Model.{u} K m),
      ∀ (L : Type u) [Field L] [IsAlgClosed L] (σ : Spec (.of L) ⟶ Spec (.of K))
        (V : Scheme.{u}) (f : V ⟶ Spec (.of L)) [IsProper f] [IsCurve L f] [Smooth f]
        [IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ f.appTop)] (_ : genus f = 9),
        ∃ i, ∃ (a : Spec (.of L) ⟶ (D i).parameter) (q : V ⟶ (D i).total)
          (κ : V ⟶ projectiveSpaceOverRing 39 (.of L)),
          IsPullback q f (D i).projection a ∧ a ≫ (D i).structureMap = σ ∧
          IsClosedImmersion κ ∧ κ ≫ (projectiveSpaceOverRing 39 (.of L) ↘ Spec (.of L)) = f ∧
          q ≫ (D i).ambientMap = κ ≫ projectiveSpaceOverMap 39 (a ≫ (D i).coefficientMap) ∧
          Nonempty ((Scheme.Modules.pullback κ).obj (twistOver 39 (Spec (.of L)) 1) ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          Nonempty ((Scheme.Modules.pullback q).obj (D i).line ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          ∀ hd : topologicalKrullDim V ≤ 1,
            invertibleCurveDegree L f hd ((Scheme.Modules.pullback q).obj (D i).line) = 48 := by
  classical
  obtain ⟨m,t,n,A,haff,hcov⟩ := GenusNineBoundedPolarizedModels.exists_finite_affine_models.{u}
  let D : (Σ i : Fin t, Fin (n i)) → Model.{u} K m := fun i => ⟨A i,haff i⟩
  refine ⟨m,t,n,D,?_⟩
  intro L _ _ σ V f _ _ _ _ hg
  obtain ⟨i,a,q,κ,sq,hκ,hbase,htriangle,⟨eκ⟩,⟨eN⟩,_⟩ := hcov L V f hg
  obtain ⟨a',q',ha',hs',hq',sq'⟩ :=
    PolarizedCurveGroundFieldBaseChange.exists_original_curve_lift (A i).projection
      ((D i).integerStructure) K a q f σ sq
  have eLine : (Scheme.Modules.pullback q').obj (D i).line ≅
      GenusNineTricanonicalCohomology.tricanonical f :=
    PolarizedCurveGroundFieldBaseChange.fieldLineIso (A i).projection (D i).integerStructure K
      (A i).line q' ≪≫ (Scheme.Modules.pullbackCongr hq').app (A i).line ≪≫ eN
  refine ⟨i,a',q',κ,sq',hs',hκ,hbase,?_,⟨eκ⟩,⟨eLine⟩,?_⟩
  · have hc : a' ≫ (D i).coefficientMap = a ≫ (A i).coefficientMap := by
      change a' ≫ (D i).parameterMap ≫ (A i).coefficientMap = _
      rw [← Category.assoc,ha']
    change q' ≫ (D i).totalMap ≫ (A i).ambientMap =
      κ ≫ projectiveSpaceOverMap 39 (a' ≫ (D i).coefficientMap)
    rw [← Category.assoc,hq',hc]
    exact htriangle
  · intro hd
    exact (invertibleCurveDegree_eq_of_iso L f hd eLine).trans
      (GenusNineTricanonicalCohomology.tricanonical_degree f hd hg)

end M9Native.GenusNineGroundFieldPolarizedModels
end

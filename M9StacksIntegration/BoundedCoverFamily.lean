module

public import M9StacksIntegration.NoetherianCurveCoverAvoidance
public import M9StacksIntegration.StandaloneCurveCohomology

/-! Actual finite bounded-cover families and simultaneous image avoidance.
The source parameter need not be integral or reduced: the real component
construction is applied inside the proved Noetherian avoidance theorem. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace M9Native

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange
  ConstantP1CoverDegreeBaseChange

/-- The original data produced by an actual fixed-Hilbert cover scheme.
Every field-cover condition concerns the genuine original pullback and
its native function-field degree. -/
structure BoundedCoverFamily (B : BigFppfSite.{u}) (K : Type u) [Field K] where
  parameter : Scheme.{u}
  total : Scheme.{u}
  parameterContained : B.Contains parameter
  totalContained : B.Contains total
  projection : total ⟶ parameter
  schemeCurve : M9StandaloneDraft.SchemeCurve projection 9
  structureMap : parameter ⟶ Spec (.of K)
  finiteType : LocallyOfFiniteType structureMap
  noetherian : IsNoetherian parameter
  lineMap : total ⟶ Line K
  lineMap_over : lineMap ≫ toBase K = projection ≫ structureMap
  fieldCover : letI : IsProper projection := schemeCurve.1
    ∀ (L : Type u) [Field L] (_ : B.Contains (Spec (.of L)))
    (a : Spec (.of L) ⟶ parameter),
    ∃ hc : IsCurve L (pullback.snd projection a),
      letI := hc
      ∃ hnc : ¬ ∃ y : Line L, ∀ c : (pullback projection a : Scheme.{u}),
        (fieldMap K projection structureMap lineMap lineMap_over L a).base c = y,
        genus (pullback.snd projection a) = 9 ∧
          fieldDegree K L projection structureMap lineMap lineMap_over a hnc ≤ 5

attribute [instance] BoundedCoverFamily.finiteType BoundedCoverFamily.noetherian

namespace BoundedCoverFamily

instance proper {B : BigFppfSite.{u}} {K : Type u} [Field K]
    (D : BoundedCoverFamily B K) : IsProper D.projection := D.schemeCurve.1

instance smooth {B : BigFppfSite.{u}} {K : Type u} [Field K]
    (D : BoundedCoverFamily B K) : SmoothOfRelativeDimension 1 D.projection := D.schemeCurve.2.1

section BaseChange

variable {B : BigFppfSite.{u}} {K : Type u} [Field K]

/-- The unchanged original pullback of a genuine bounded-cover family
again has its genuine cover data. This is the raw source used by the
actual native atlas fibre product. -/
def baseChange (D : BoundedCoverFamily B K) {P : Scheme.{u}}
    (hP : B.Contains P) (f : P ⟶ D.parameter) [IsNoetherian P]
    [LocallyOfFiniteType (f ≫ D.structureMap)] : BoundedCoverFamily B K where
  parameter := P
  total := pullback D.projection f
  parameterContained := hP
  totalContained := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (pullback.snd D.projection f) hP
  projection := pullback.snd D.projection f
  schemeCurve := M9StacksIntegration.StandaloneCurveCohomology.schemeCurve_of_isPullback
    D.projection (pullback.snd D.projection f) (pullback.fst D.projection f) f
    (IsPullback.of_hasPullback D.projection f) D.schemeCurve
  structureMap := f ≫ D.structureMap
  finiteType := inferInstance
  noetherian := inferInstance
  lineMap := changedLineMap K D.projection D.lineMap f
  lineMap_over := changedLineMap_over K D.projection D.structureMap D.lineMap D.lineMap_over f
  fieldCover := by
    intro L _ hL a
    obtain ⟨hc,hcov⟩ := D.fieldCover L hL (a ≫ f)
    letI := hc
    obtain ⟨hnc,hgen,hdeg⟩ := hcov
    have hc' : IsCurve L (pullback.snd (pullback.snd D.projection f) a) :=
      changedField_isCurve L D.projection f a
    refine ⟨hc',?_⟩
    letI := hc'
    have hn' := fieldMap_change_nonconstant K D.projection D.structureMap
      D.lineMap D.lineMap_over L f a hnc
    refine ⟨hn',(fieldGenus_change L D.projection f a).trans hgen,?_⟩
    rw [fieldDegree_change K L D.projection D.structureMap D.lineMap D.lineMap_over f a hnc]
    exact hdeg

end BaseChange

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)

abbrev originalFamily (D : BoundedCoverFamily B K) : CurveFamily B hZ :=
  CurveClassifierPullback.originalFamily B hZ D.totalContained D.parameterContained D.projection

/-- Noetherian parameter-image nondominance, with all source integral
components constructed by the genuine finite component theorem. -/
theorem not_isDominant (D : BoundedCoverFamily B K)
    (R : CurveFamily B hZ) (sR : B.inclusion.obj R.base.left ⟶ Spec (.of K))
    [LocallyOfFiniteType sR] [IsIntegral (B.inclusion.obj R.base.left)]
    (β : D.originalFamily B hZ K ⟶ R)
    (hβ : B.inclusion.map β.baseMap.left ≫ sR = D.structureMap)
    (hR : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg R sR)) :
    ¬ IsDominant (B.inclusion.map β.baseMap.left) := by
  obtain ⟨U,_,hne,hdisj⟩ :=
    NoetherianCurveCoverAvoidance.exists_dense_open_avoiding_parameterImage B hZ K hK hAlg
      D.totalContained D.parameterContained D.projection D.structureMap R sR β hβ hR
      D.lineMap D.lineMap_over D.fieldCover
  intro hdom
  have hd := (isDominant_iff (B.inclusion.map β.baseMap.left)).mp hdom
  obtain ⟨x,hxU,hx⟩ := hd.inter_open_nonempty (U : Set (B.inclusion.obj R.base.left))
    U.isOpen hne
  exact Set.disjoint_left.mp hdisj hx hxU

/-- Finitely many actual bounded-cover families miss a common genuine
dense open of each actual smooth integral atlas piece. -/
theorem exists_dense_open_avoiding_finite_parameterImages
    {ι : Type v} [Finite ι] (D : ι → BoundedCoverFamily B K)
    (R : CurveFamily B hZ) (sR : B.inclusion.obj R.base.left ⟶ Spec (.of K))
    [LocallyOfFiniteType sR] [IsIntegral (B.inclusion.obj R.base.left)]
    (β : ∀ i, (D i).originalFamily B hZ K ⟶ R)
    (hβ : ∀ i, B.inclusion.map (β i).baseMap.left ≫ sR = (D i).structureMap)
    (hR : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg R sR)) :
    ∃ U : (B.inclusion.obj R.base.left).Opens,
      Dense (U : Set (B.inclusion.obj R.base.left)) ∧
      (U : Set (B.inclusion.obj R.base.left)).Nonempty ∧
      ∀ i, Disjoint (Set.range (B.inclusion.map (β i).baseMap.left).base)
        (U : Set (B.inclusion.obj R.base.left)) :=
  TangentImageAvoidance.exists_dense_open_avoiding_finite_nondominant
    (fun i => (D i).parameter) (B.inclusion.obj R.base.left)
    (fun i => B.inclusion.map (β i).baseMap.left)
    (fun i => (D i).not_isDominant B hZ K hK hAlg R sR (β i) (hβ i) hR)

end BoundedCoverFamily
end M9Native
end

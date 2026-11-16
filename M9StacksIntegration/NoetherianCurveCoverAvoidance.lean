module

public import M9StacksIntegration.CurveCoverNondominance
public import M9StacksIntegration.FiniteIntegralComponentCover
public import M9StacksIntegration.TangentImageAvoidance

/-!
# Actual cover images from arbitrary Noetherian parameter schemes

The parameter scheme may be singular or nonreduced. Its actual finitely
many reduced irreducible component schemes carry the genuine pullback
cover families and Cartesian family arrows. Componentwise nondominance
therefore gives an actual dense open avoiding the entire original image.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.NoetherianCurveCoverAvoidance

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange
  ConstantP1CoverDegreeBaseChange FiniteIntegralComponentCover

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K)) [LocallyOfFiniteType s] [IsNoetherian T]

/-- The actual image of a genuine bounded-cover family over ANY
Noetherian parameter scheme misses a nonempty dense open of the actual
integral target atlas piece. Integral source pieces and all their cover
data are constructed, rather than assumed. -/
theorem exists_dense_open_avoiding_parameterImage
    (R : CurveFamily B hZ) (sR : B.inclusion.obj R.base.left ⟶ Spec (.of K))
    [LocallyOfFiniteType sR] [IsIntegral (B.inclusion.obj R.base.left)]
    (β : CurveClassifierPullback.originalFamily B hZ hX hT p ⟶ R)
    (hβ : B.inclusion.map β.baseMap.left ≫ sR = s)
    (hR : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK hAlg R sR))
    (g : X ⟶ Line K) (hg : g ≫ toBase K = p ≫ s)
    (hcover : ∀ (L : Type u) [Field L] (_ : B.Contains (Spec (.of L)))
      (a : Spec (.of L) ⟶ T),
      ∃ hc : IsCurve L (pullback.snd p a),
        letI := hc
        ∃ hnc : ¬ ∃ y : Line L, ∀ c : (pullback p a : Scheme.{u}),
          (fieldMap K p s g hg L a).base c = y,
          genus (pullback.snd p a) = 9 ∧ fieldDegree K L p s g hg a hnc ≤ 5) :
    ∃ U : (B.inclusion.obj R.base.left).Opens,
      Dense (U : Set (B.inclusion.obj R.base.left)) ∧
      (U : Set (B.inclusion.obj R.base.left)).Nonempty ∧
      Disjoint (Set.range (B.inclusion.map β.baseMap.left).base)
        (U : Set (B.inclusion.obj R.base.left)) := by
  let C := component T
  let j := inclusion T
  have hC : ∀ i : Index T, B.Contains (C i) := fun i => contains_component T B hT i
  have hXC : ∀ i : Index T, B.Contains (pullback p (j i)) := fun i =>
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.snd p (j i)) (hC i)
  let βC := fun i : Index T => CurveFieldClassifierComposition.pullbackFamilyArrow B hZ
    hX hT (hC i) p (j i) (hXC i) ≫ β
  have hβC : ∀ i : Index T, B.inclusion.map (βC i).baseMap.left ≫ sR = j i ≫ s := by
    intro i
    change (j i ≫ B.inclusion.map β.baseMap.left) ≫ sR = j i ≫ s
    rw [Category.assoc, hβ]
  have hn : ∀ i : Index T, ¬ IsDominant (B.inclusion.map (βC i).baseMap.left) := by
    intro i
    have : LocallyOfFiniteType (j i ≫ s) := inferInstance
    apply CurveCoverNondominance.not_isDominant_parameterMap B hZ K hK hAlg
      (hXC i) (hC i) (pullback.snd p (j i)) (j i ≫ s) R sR (βC i) (hβC i) hR
      (changedLineMap K p g (j i)) (changedLineMap_over K p s g hg (j i))
    intro L _ hL a
    obtain ⟨hc,hcov⟩ := hcover L hL (a ≫ j i)
    letI := hc
    obtain ⟨hnc,hgen,hdeg⟩ := hcov
    have hc' : IsCurve L (pullback.snd (pullback.snd p (j i)) a) :=
      changedField_isCurve L p (j i) a
    refine ⟨hc', ?_⟩
    letI := hc'
    have hn' := fieldMap_change_nonconstant K p s g hg L (j i) a hnc
    refine ⟨hn', (fieldGenus_change L p (j i) a).trans hgen, ?_⟩
    rw [fieldDegree_change K L p s g hg (j i) a hnc]
    exact hdeg
  obtain ⟨U,hden,hne,hdisj⟩ :=
    TangentImageAvoidance.exists_dense_open_avoiding_finite_nondominant C
      (B.inclusion.obj R.base.left) (fun i => B.inclusion.map (βC i).baseMap.left) hn
  refine ⟨U,hden,hne,Set.disjoint_left.mpr ?_⟩
  intro y hy hyU
  obtain ⟨t,rfl⟩ := hy
  obtain ⟨i,c,hc⟩ := exists_component_point T t
  apply Set.disjoint_left.mp (hdisj i) _ hyU
  refine ⟨c, ?_⟩
  change (j i ≫ B.inclusion.map β.baseMap.left) c = (B.inclusion.map β.baseMap.left) t
  rw [Scheme.Hom.comp_apply, hc]
  rfl

end M9Native.NoetherianCurveCoverAvoidance
end

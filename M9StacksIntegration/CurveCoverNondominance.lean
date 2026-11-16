module

public import M9StacksIntegration.ConstantP1CoverPointCoordinates
public import M9StacksIntegration.CurveCoverSmoothClassifierObstruction
public import M9StacksIntegration.DominantSmoothClosedPoint

/-!
# Genuine bounded cover families cannot dominate a smooth curve atlas

A hypothetical dominant original parameter map has a nonempty actual
smooth locus. The SAME cover family is restricted to that open. Its
original field covers, genus and native degree are transported by the
proved pullback-pasting laws, and contradict the actual smooth-classifier
H1 obstruction at a closed point of that open.

This does not construct the bounded cover parameter spaces or assume
their dimension. Fields outside the fixed native cutoff remain a separate
original all-test coverage gate. Every site-bounded field-cover hypothesis concerns the actual
original curve and the native function-field degree.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.CurveCoverNondominance

open PencilProjectiveLineGeometry ConstantP1CoverBaseChange
  ConstantP1CoverDegreeBaseChange

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (p : X ⟶ T) [IsProper p] [SmoothOfRelativeDimension 1 p]
  (s : T ⟶ Spec (.of K)) [LocallyOfFiniteType s]
  [IsIntegral T]

local instance originalSmooth : Smooth p := SmoothOfRelativeDimension.smooth 1 p

/-- A genuine family of nonconstant degree-at-most-five genus-nine
covers cannot dominate the original base of a smooth curve-family
classifier. The target family may have an algebraic-space total space. -/
theorem not_isDominant_parameterMap
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
    ¬ IsDominant (B.inclusion.map β.baseMap.left) := by
  intro hdom
  let f : T ⟶ B.inclusion.obj R.base.left := B.inclusion.map β.baseMap.left
  have : IsDominant f := hdom
  have : LocallyOfFiniteType (f ≫ sR) := by
    change LocallyOfFiniteType (B.inclusion.map β.baseMap.left ≫ sR)
    rw [hβ]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sR
  have : IsLocallyNoetherian (B.inclusion.obj R.base.left) :=
    LocallyOfFiniteType.isLocallyNoetherian sR
  let U : T.Opens := f.smoothLocus
  have hU : (U : Set T).Nonempty := DominantSmoothClosedPoint.smoothLocus_nonempty K s sR f
  have : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  have hsm : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      eq_top_iff]
    intro x _
    exact x.2
  have hUSite : B.Contains U := Scheme.size_lt_of_isOpenImmersion U.ι hT
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace (U.ι ≫ s)
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set U).Nonempty) isOpen_univ.isLocallyClosed
  let κ := IsLocalRing.ResidueField (U.toScheme.presheaf.stalk x)
  let i : Spec (.of κ) ⟶ U := U.toScheme.fromSpecResidueField x
  let a : Spec (.of κ) ⟶ T := i ≫ U.ι
  have hk : B.Contains (Spec (.of κ)) := B.residueField_spec_contains hUSite x
  obtain ⟨hc, hcov⟩ := hcover κ hk a
  have : IsCurve κ (pullback.snd p a) := hc
  obtain ⟨hnc, hgen, hdegree⟩ := hcov
  let pU := pullback.snd p U.ι
  let sU := U.ι ≫ s
  let gU := changedLineMap K p g U.ι
  have hgU : gU ≫ toBase K = pU ≫ sU := changedLineMap_over K p s g hg U.ι
  have : IsCurve κ (pullback.snd pU i) := changedField_isCurve κ p U.ι i
  have : IsCurve κ (ParameterTangentDeformation.fibre pU x).hom :=
    inferInstanceAs (IsCurve κ (pullback.snd pU i))
  have hgenU : genus (ParameterTangentDeformation.fibre pU x).hom = 9 :=
    (fieldGenus_change κ p U.ι i).trans hgen
  have hnU := fieldMap_change_nonconstant K p s g hg κ U.ι i hnc
  have hdU : fieldDegree K κ pU sU gU hgU i hnU ≤ 5 := by
    rw [fieldDegree_change K κ p s g hg U.ι i hnc]
    exact hdegree
  have hnOriginal := ConstantP1CoverPointCoordinates.originalPointMap_nonconstant
    K pU sU gU hgU x hnU
  have hdOriginal : ParameterP1SourceImage.pointDegree K sU pU
      (familyMap K pU sU gU hgU) (familyMap_over K pU sU gU hgU) x hnOriginal ≤ 5 := by
    rw [ConstantP1CoverPointCoordinates.pointDegree_eq_fieldDegree K pU sU gU hgU x hnU]
    exact hdU
  have hXUSite : B.Contains (pullback p U.ι) :=
    Scheme.size_lt_of_isOpenImmersion (pullback.fst p U.ι) hX
  let βU := CurveFieldClassifierComposition.pullbackFamilyArrow B hZ
    hX hT hUSite p U.ι hXUSite ≫ β
  have hβU : B.inclusion.map βU.baseMap.left ≫ sR = sU := by
    change (U.ι ≫ B.inclusion.map β.baseMap.left) ≫ sR = U.ι ≫ s
    rw [Category.assoc, hβ]
  have hsmU : Smooth (B.inclusion.map βU.baseMap.left) := by
    change Smooth (U.ι ≫ f)
    exact hsm
  exact CurveCoverSmoothClassifierObstruction.not_smooth_parameterMap B hZ K hK hAlg
    hXUSite hUSite pU sU x R sR βU hβU hR
    (familyMap K pU sU gU hgU) (familyMap_over K pU sU gU hgU)
    hx.2 hgenU hnOriginal hdOriginal hsmU

/-- The actual image of such an integral cover-parameter family misses
an actual dense nonempty open of the original integral target component.
No parameter-space dimension bound is used. -/
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
  let f : T ⟶ B.inclusion.obj R.base.left := B.inclusion.map β.baseMap.left
  have hn := not_isDominant_parameterMap B hZ K hK hAlg hX hT p s R sR β hβ hR g hg hcover
  have hproper : closure (Set.range f.base) ≠ Set.univ := by
    intro heq
    apply hn
    exact (isDominant_iff f).mpr (dense_iff_closure_eq.mpr heq)
  let U : (B.inclusion.obj R.base.left).Opens :=
    ⟨(closure (Set.range f.base))ᶜ, isClosed_closure.isOpen_compl⟩
  have hnonempty : (U : Set (B.inclusion.obj R.base.left)).Nonempty :=
    (Set.ne_univ_iff_exists_notMem _).mp hproper
  refine ⟨U, U.isOpen.dense hnonempty, hnonempty, ?_⟩
  exact Set.disjoint_left.mpr (fun y hy hyU => hyU (subset_closure hy))

end M9Native.CurveCoverNondominance

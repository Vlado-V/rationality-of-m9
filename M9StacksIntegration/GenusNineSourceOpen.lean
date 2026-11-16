module

public import M9StacksIntegration.ProperSmoothLocus
public import M9StacksIntegration.SmoothConnectedCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Curves.StableLocus.StableCurveLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable

/-!
# The actual smooth genus-nine source open of a flat equation family

The open is the intersection of the true stable genus-nine locus and the
complement of the image of the original non-smooth locus. Its field-point
criterion uses every original field-valued point, without a site cutoff.
The entire restricted family is smooth of relative dimension one; its
actual field fibres are integral native curves with constant functions
and genus nine. No property is imposed on the other universal-form fibres.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.GenusNineSourceOpen

variable {X T : Scheme.{u}} (p : X ⟶ T)
  [IsProper p] [Flat p] [LocallyOfFinitePresentation p]

/-- Membership in the original proper smooth base locus is equivalent to
smoothness of the SAME original fibre in any cartesian field square. -/
theorem mem_smoothOpen_iff {K : Type u} [Field K] {V : Scheme.{u}}
    {y : Spec (.of K) ⟶ T} {q : V ⟶ X} {f : V ⟶ Spec (.of K)}
    (sq : IsPullback q f p y) :
    y (IsLocalRing.closedPoint K) ∈ ProperSmoothLocus.goodOpen p ↔ Smooth f := by
  have : LocallyOfFinitePresentation f :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq inferInstance
  rw [ProperSmoothLocus.mem_goodOpen_iff,
    ← Scheme.Hom.smoothLocus_eq_top_iff,
    Scheme.Hom.smoothLocus_eq_preimage_of_isPullback sq (Or.inl inferInstance)]
  have hr := range_eq_preimage_range_of_isPullback sq
  have hy : Set.range y = {y (IsLocalRing.closedPoint K)} := by
    ext t
    refine ⟨?_, fun ht => ⟨IsLocalRing.closedPoint K, ht.symm⟩⟩
    rintro ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    rfl
  constructor
  · intro h
    refine top_le_iff.mp fun v _ => h (q v) ?_
    have hv : q v ∈ p ⁻¹' Set.range y := hr ▸ ⟨v, rfl⟩
    rwa [hy] at hv
  · intro h z hz
    obtain ⟨v, rfl⟩ : z ∈ Set.range q := by rwa [hr, hy]
    exact (h ▸ trivial : v ∈ q ⁻¹ᵁ p.smoothLocus)

/-- The genuine smooth stable genus-nine locus is open, with a criterion
on every original field-valued fibre. -/
theorem exists_sourceOpen [IsNoetherian T] :
    ∃ U : T.Opens, Smooth (p ∣_ U) ∧
      ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ T)
        (q : V ⟶ X) (f : V ⟶ Spec (.of K)) [IsProper f], IsPullback q f p y →
        (y (IsLocalRing.closedPoint K) ∈ U ↔
          Smooth f ∧ IsStableCurveOfGenusOverField K f 9) := by
  obtain ⟨W, hW⟩ := exists_opens_forall_mem_iff_isStableCurveOfGenusOverField p 9
  let U := ProperSmoothLocus.goodOpen p ⊓ W
  have hpre : ((p ⁻¹ᵁ U : X.Opens) : Set X) ⊆ (p.smoothLocus : Set X) := by
    intro x hx
    exact ProperSmoothLocus.preimage_subset_smoothLocus p hx.1
  have hcomp : Smooth ((p ⁻¹ᵁ U).ι ≫ p) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    exact fun x _ => hpre x.2
  have hsm : Smooth (p ∣_ U) :=
    MorphismProperty.of_postcomp (@Smooth) (W' := MorphismProperty.monomorphisms Scheme)
      (p ∣_ U) U.ι inferInstance (by rw [morphismRestrict_ι]; exact hcomp)
  refine ⟨U, hsm, fun K _ V y q f _ sq => ?_⟩
  change (y (IsLocalRing.closedPoint K) ∈ ProperSmoothLocus.goodOpen p ∧
    y (IsLocalRing.closedPoint K) ∈ W) ↔ _
  rw [mem_smoothOpen_iff p sq, hW K V y q f sq]

/-- Smoothness and the actual stable fibre conditions give the native
curve structure, original constants map and original genus. -/
theorem field_geometry {K : Type u} [Field K] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of K)) [IsProper f] [Smooth f]
    (h : IsStableCurveOfGenusOverField K f 9) :
    IsCurve K f ∧ topologicalKrullDim V = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) ∧ genus f = 9 := by
  obtain ⟨_, hd, hH0, hg, _⟩ := h
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) := hH0
  exact ⟨SmoothConnectedCurve.isCurve_of_smooth_constantFunctions f hd, hd, hH0, hg⟩

/-- Every original smooth proper genus-nine curve with its actual
constant-functions map belongs to the stable locus used above. -/
theorem stable_of_original_curve {K : Type u} [Field K] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (hg : genus f = 9) :
    IsStableCurveOfGenusOverField K f 9 := by
  let : V.Over (Spec (.of K)) := ⟨f⟩
  have : IsProper (V ↘ Spec (.of K)) := ‹IsProper f›
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (V ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop))
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve K f
  have hn := isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension f
  obtain ⟨_, hd, hnodal⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_of_field K f).mp hn
  have hg' : 2 ≤ genus (V ↘ Spec (.of K)) := by change 2 ≤ genus f; rw [hg]; norm_num
  obtain ⟨_, hamp⟩ := isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    K V hd hnodal (not_isRationalTail_of_irreducibleSpace K V)
    (not_isRationalBridge_of_irreducibleSpace K V) hg'
  refine ⟨hnodal, hd, ?_, hg, hamp⟩
  change IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)
  infer_instance

/-- The entire smooth family has relative dimension one, as derived from
its actual stable fibres over the original residue fields. -/
theorem smoothRelativeDimension_of_fieldFibres [Smooth p]
    (h : ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ T)
      (q : V ⟶ X) (f : V ⟶ Spec (.of K)) [IsProper f], IsPullback q f p y →
        IsStableCurveOfGenusOverField K f 9) :
    SmoothOfRelativeDimension 1 p := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq p 1 fun x => ?_
  have : IsProper (p.fiberToSpecResidueField (p x)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback p _) inferInstance
  obtain ⟨_, hd, hH0, _, _⟩ := h (T.residueField (p x)) (p.fiber (p x))
    (T.fromSpecResidueField (p x)) (p.fiberι (p x)) (p.fiberToSpecResidueField (p x))
    (IsPullback.of_hasPullback p _)
  change topologicalKrullDim (p.fiber (p x)) = 1 at hd
  change IsIso ((Scheme.ΓSpecIso (.of (T.residueField (p x)))).inv ≫
    (p.fiberToSpecResidueField (p x)).appTop) at hH0
  have : ConnectedSpace (p.fiber (p x)) :=
    @connectedSpace_of_isIso_globalSections (T.residueField (p x)) _ _ _ hH0
  have : IsLocallyNoetherian (p.fiber (p x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField (p x))
  have : CompactSpace (p.fiber (p x)) :=
    QuasiCompact.compactSpace_of_compactSpace (p.fiberToSpecResidueField (p x))
  have : IsNoetherian (p.fiber (p x)) := ⟨⟩
  have heq : Equidimensional (p.fiber (p x)) :=
    equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hd
  exact topologicalKrullDimAt_eq_of_equidimensional (T.residueField (p x))
    (p.fiber (p x)) (p.fiberToSpecResidueField (p x)) heq hd (p.asFiber x)

/-- A finite flat equation model admits an actual open on which it is a
smooth relative curve and all original field fibres have genus nine. -/
theorem exists_sourceOpen_curve [IsNoetherian T] :
    ∃ U : T.Opens, SmoothOfRelativeDimension 1 (p ∣_ U) ∧
      (∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ U)
        (q : V ⟶ p ⁻¹ᵁ U) (f : V ⟶ Spec (.of K)) [IsProper f],
        IsPullback q f (p ∣_ U) y →
          IsCurve K f ∧ topologicalKrullDim V = 1 ∧
            IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) ∧ genus f = 9) ∧
      (∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ T)
        (q : V ⟶ X) (f : V ⟶ Spec (.of K)) [IsProper f], IsPullback q f p y →
        (y (IsLocalRing.closedPoint K) ∈ U ↔
          Smooth f ∧ IsStableCurveOfGenusOverField K f 9)) := by
  obtain ⟨U, hs, hU⟩ := exists_sourceOpen p
  have : Smooth (p ∣_ U) := hs
  have hst : ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ U)
      (q : V ⟶ p ⁻¹ᵁ U) (f : V ⟶ Spec (.of K)) [IsProper f],
      IsPullback q f (p ∣_ U) y → IsStableCurveOfGenusOverField K f 9 := by
    intro K _ V y q f _ sq
    have hbig := sq.paste_horiz (isPullback_morphismRestrict p U).flip
    exact ((hU K V (y ≫ U.ι) (q ≫ (p ⁻¹ᵁ U).ι) f hbig).mp
      (y (IsLocalRing.closedPoint K)).2).2
  refine ⟨U, smoothRelativeDimension_of_fieldFibres (p ∣_ U) hst, ?_, hU⟩
  intro K _ V y q f _ sq
  have : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) sq hs
  exact field_geometry f (hst K V y q f sq)

/-- The actual source open covers every original smooth proper
genus-nine curve presented as a fibre of the equation family. The lifted
cartesian square retains both original projection maps. -/
theorem exists_sourceOpen_covering_original_curves [IsNoetherian T] :
    ∃ U : T.Opens, SmoothOfRelativeDimension 1 (p ∣_ U) ∧
      (∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ U)
        (q : V ⟶ p ⁻¹ᵁ U) (f : V ⟶ Spec (.of K)) [IsProper f],
        IsPullback q f (p ∣_ U) y →
          IsCurve K f ∧ topologicalKrullDim V = 1 ∧
            IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) ∧ genus f = 9) ∧
      (∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (.of K) ⟶ T)
        (q : V ⟶ X) (f : V ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
        [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (_ : genus f = 9),
        IsPullback q f p y →
          ∃ (y' : Spec (.of K) ⟶ U) (q' : V ⟶ p ⁻¹ᵁ U),
            y' ≫ U.ι = y ∧ q' ≫ (p ⁻¹ᵁ U).ι = q ∧
              IsPullback q' f (p ∣_ U) y') := by
  obtain ⟨U, hsm, hgeom, hU⟩ := exists_sourceOpen_curve p
  refine ⟨U, hsm, hgeom, ?_⟩
  intro K _ V y q f _ _ _ _ hg sq
  have hy := (hU K V y q f sq).mpr ⟨inferInstance, stable_of_original_curve f hg⟩
  exact exists_isPullback_restrict_of_mem p U sq hy

end M9Native.GenusNineSourceOpen
end

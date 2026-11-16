module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Stalk
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Regular
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.DimensionCriterion
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothEquidimensionalOverField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Full finite zero schemes of sections of the expected rank are regular

The section's actual rank-r coordinate ideal is used without taking a radical.
At a generic point of its full finite zero scheme, the ambient smooth stalk has
dimension r and is Cohen--Macaulay, while its actual quotient has dimension zero.
The native dimension criterion therefore makes the actual r generators regular.
No transversality or regularity of a prefix of cuts is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow
universe u

namespace M9Native.FiniteZeroRegularity

/-- Every point of a scheme finite over the original field is closed.
This uses the actual discrete fibre, including all nonreduced structure. -/
theorem isClosed_point_of_isFinite (K : Type u) [Field K] {Y : Scheme.{u}}
    (t : Y ⟶ Spec (.of K)) [IsFinite t] (y : Y) : IsClosed ({y} : Set Y) := by
  have hd := t.isDiscrete_preimage_singleton (t y)
  have huniv : t ⁻¹' {t y} = Set.univ :=
    Set.eq_univ_of_forall fun z => Subsingleton.elim (t z) (t y)
  rw [huniv] at hd
  let : DiscreteTopology Y := by
    have := hd.to_subtype
    exact (Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology
  exact isClosed_discrete _

/-- Over the original field the unique fibre is the actual source,
so smooth relative dimension computes its actual local dimension. -/
theorem localDimension_of_smooth_relative_dimension (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (r : ℕ)
    [SmoothOfRelativeDimension r f] (x : X) :
    topologicalKrullDimAt X x = (r : WithBot ℕ∞) := by
  have hpre : f ⁻¹' {f x} = Set.univ :=
    Set.eq_univ_of_forall fun z => Subsingleton.elim (f z) (f x)
  have hpoint : (f.fiberHomeo (f x)) (f.asFiber x) = ⟨x,rfl⟩ := by
    apply Subtype.ext
    simp [Scheme.Hom.asFiber]
  have h₁ := topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f x)) (f.asFiber x)
  rw [hpoint] at h₁
  have h₂ := topologicalKrullDimAt_eq_of_homeomorph
    ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X)) ⟨x,rfl⟩
  exact h₂.symm.trans (h₁.symm.trans (fiberDimensionAt_eq_of_smoothOfRelativeDimension f r x))

/-- At a closed point the actual ambient regular local ring has the
same dimension as the original smooth scheme. -/
theorem closed_stalk_dimension (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (r : ℕ) [SmoothOfRelativeDimension r f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = (r : WithBot ℕ∞) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth r f
  exact (topologicalKrullDimAt_eq_krullDimOfRing_stalk K X f x hx).symm.trans
    (localDimension_of_smooth_relative_dimension K f r x)

/-- Actual regular generators of the full section ideal at every generic
zero point. Nilpotents are retained in the actual stalk quotient. -/
theorem stalk_regular_sequence_of_finite_zero (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (r : ℕ)
    [SmoothOfRelativeDimension r f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] (s : Γ(E, ⊤))
    [IsFinite ((zeroSchemeOfSection X E s).subschemeι ≫ f)]
    (ξ : genericPoints (zeroSchemeOfSection X E s).subscheme) :
    ∃ rs : List (X.presheaf.stalk ((zeroSchemeOfSection X E s).subschemeι ξ.1)),
      rs.length = r ∧
      RingTheory.Sequence.IsRegular
        (X.presheaf.stalk ((zeroSchemeOfSection X E s).subschemeι ξ.1)) rs ∧
      Ideal.ofList rs = RingHom.ker
        ((zeroSchemeOfSection X E s).subschemeι.stalkMap ξ.1).hom := by
  let I := zeroSchemeOfSection X E s
  let x : X := I.subschemeι ξ.1
  let R := X.presheaf.stalk x
  let φ : R →+* I.subscheme.presheaf.stalk ξ.1 := (I.subschemeι.stalkMap ξ.1).hom
  let : Smooth f := SmoothOfRelativeDimension.smooth r f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsRegularLocalRing R := (isRegular_of_smooth_over_field f).isRegularLocalRing_stalk x
  have hy := isClosed_point_of_isFinite K (I.subschemeι ≫ f) ξ.1
  have hx : IsClosed ({x} : Set X) := by
    change IsClosed ({I.subschemeι ξ.1} : Set X)
    rw [← Set.image_singleton]
    exact I.subschemeι.isClosedEmbedding.isClosedMap _ hy
  have hdim : ringKrullDim R = (r : WithBot ℕ∞) := closed_stalk_dimension K f r x hx
  obtain ⟨g,hg⟩ := SectionZeroScheme.exists_stalk_eq_span E r s x
  let rs : List R := List.ofFn g
  have hlen : rs.length = r := List.length_ofFn
  have hspan : Ideal.ofList rs = RingHom.ker φ := by
    dsimp only [rs]
    rw [Ideal.ofList_ofFn]
    exact hg.symm.trans (IdealSheafData.ker_subschemeι_stalkMap_eq I ξ.1).symm
  have hxs : ∀ a ∈ rs, a ∈ IsLocalRing.maximalIdeal R := by
    intro a ha
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
    rw [← hspan]
    exact Ideal.subset_span ha
  have hsurj : Function.Surjective φ := I.subschemeι.stalkMap_surjective ξ.1
  have hquot : ringKrullDim (R ⧸ Ideal.ofList rs) = 0 := by
    rw [hspan, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)]
    exact ringKrullDim_stalk_eq_zero_of_mem_genericPoints I.subscheme ξ.1 ξ.2
  have hCM : Module.IsMaximalCohenMacaulay R R :=
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay R).mp
      (IsRegularLocalRing.isCohenMacaulayLocalRing R)
  have hreg : RingTheory.Sequence.IsRegular R rs :=
    (hCM.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim rs hxs).1.mpr
      (by simp [hquot,hlen,hdim])
  exact ⟨rs,hlen,hreg,hspan⟩

/-- The exact native 0FA9 hypothesis follows from finiteness of the full
zero scheme and actual smooth relative dimension equal to the actual rank.
It holds for every Chow base and every dimension stratum. -/
theorem isRegularZeroSchemeSequence_of_finite_zero (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (r : ℕ)
    [SmoothOfRelativeDimension r f] (C : ChowSituation.{u}) (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] (s : Γ(E, ⊤))
    [IsFinite ((zeroSchemeOfSection X E s).subschemeι ≫ f)] (m : ℤ) :
    IsRegularZeroSchemeSequence C q E s r m := by
  intro ξ _
  exact stalk_regular_sequence_of_finite_zero K f r E s ξ

/-- The ordinary smooth pure-dimensional formulation derives native
smooth relative dimension; no regular-section condition is supplied. -/
theorem isRegularZeroSchemeSequence_of_smooth_equidimensional (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f]
    (hequi : Equidimensional X) (r : ℕ) (hdim : topologicalKrullDim X = (r : WithBot ℕ∞))
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] (s : Γ(E, ⊤))
    [IsFinite ((zeroSchemeOfSection X E s).subschemeι ≫ f)] (m : ℤ) :
    IsRegularZeroSchemeSequence C q E s r m := by
  let : SmoothOfRelativeDimension r f :=
    smoothOfRelativeDimension_of_equidimensional K f hequi r hdim
  exact isRegularZeroSchemeSequence_of_finite_zero K f r C q E s m

/-- Four genuine equations on an actual smooth pure fourfold, with full
finite zero scheme, satisfy exactly the rank4, dimension0 native predicate. -/
theorem rank_four_regular_of_finite_zero (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 4)
    (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 4] (s : Γ(E, ⊤))
    [IsFinite ((zeroSchemeOfSection X E s).subschemeι ≫ f)] :
    IsRegularZeroSchemeSequence C q E s 4 0 :=
  isRegularZeroSchemeSequence_of_smooth_equidimensional K f hequi 4 hdim C q E s 0

end M9Native.FiniteZeroRegularity
end

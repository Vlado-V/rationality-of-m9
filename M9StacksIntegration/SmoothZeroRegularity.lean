module

public import M9StacksIntegration.FiniteZeroRegularity
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base

/-!
# Expected-rank regularity of an actual smooth full zero scheme

The ambient smooth scheme has dimension r+d and the full zero scheme
is smooth of dimension d. At each generic zero point, the dimension
formula and the actual closed-immersion residue-field isomorphism give
ambient stalk dimension r. The actual stalk quotient has dimension
zero. The genuine r section generators then form a regular sequence
by the Cohen--Macaulay dimension criterion.

There is no finiteness, regular-immersion, codimension-of-ideal, reduced
zero-locus replacement, or regular-prefix hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

universe u
namespace M9Native.SmoothZeroRegularity

/-- The genuine dimension formula computes the ambient stalk at a
generic point of an actual smooth closed subscheme. -/
theorem generic_stalk_dimension_of_smooth_subscheme (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (r d : ℕ)
    [SmoothOfRelativeDimension (r+d) f] (I : X.IdealSheafData)
    [SmoothOfRelativeDimension d (I.subschemeι ≫ f)]
    (ξ : genericPoints I.subscheme) :
    ringKrullDim (X.presheaf.stalk (I.subschemeι ξ.1)) = (r : WithBot ℕ∞) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth (r+d) f
  let : Smooth (I.subschemeι ≫ f) :=
    SmoothOfRelativeDimension.smooth d (I.subschemeι ≫ f)
  have hX := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk K X f
    (I.subschemeι ξ.1)
  have hI := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk K I.subscheme
    (I.subschemeι ≫ f) ξ.1
  rw [FiniteZeroRegularity.localDimension_of_smooth_relative_dimension K f (r+d)] at hX
  rw [FiniteZeroRegularity.localDimension_of_smooth_relative_dimension K
    (I.subschemeι ≫ f) d, ringKrullDim_stalk_eq_zero_of_mem_genericPoints
      I.subscheme ξ.1 ξ.2, add_zero,
    ← trdeg_residueField_of_surjectiveOnStalks K f I.subschemeι ξ.1] at hI
  have hsum : (d : WithBot ℕ∞) +
      ringKrullDim (X.presheaf.stalk (I.subschemeι ξ.1)) =
        (d : WithBot ℕ∞) + (r : WithBot ℕ∞) := by
    calc
      _ = ((r+d : ℕ) : WithBot ℕ∞) := by rw [hI]; exact hX.symm
      _ = _ := by simp only [Nat.cast_add]; ac_rfl
  exact ENat.WithBot.natCast_add_cancel.mp hsum

/-- The actual r coordinate generators of the full section ideal are
regular at every generic zero point. Nilpotents are retained. -/
theorem stalk_regular_sequence_of_smooth_zero (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (r d : ℕ)
    [SmoothOfRelativeDimension (r+d) f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] (s : Γ(E, ⊤))
    [SmoothOfRelativeDimension d ((zeroSchemeOfSection X E s).subschemeι ≫ f)]
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
  let : Smooth f := SmoothOfRelativeDimension.smooth (r+d) f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsRegularLocalRing R := (isRegular_of_smooth_over_field f).isRegularLocalRing_stalk x
  have hdim : ringKrullDim R = (r : WithBot ℕ∞) :=
    generic_stalk_dimension_of_smooth_subscheme K f r d I ξ
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

/-- The exact native regular-zero predicate follows from actual smooth
ambient and full-zero dimensions, for every Chow base and stratum. -/
theorem isRegularZeroSchemeSequence_of_smooth_zero (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (r d : ℕ)
    [SmoothOfRelativeDimension (r+d) f] (C : ChowSituation.{u})
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r] (s : Γ(E, ⊤))
    [SmoothOfRelativeDimension d ((zeroSchemeOfSection X E s).subschemeι ≫ f)] (m : ℤ) :
    IsRegularZeroSchemeSequence C q E s r m := by
  intro ξ _
  exact stalk_regular_sequence_of_smooth_zero K f r d E s ξ

/-- The actual rank-three, dimension-four zero scheme in a smooth
sevenfold has precisely the native regularity needed by 0FA9. -/
theorem rank_three_regular_of_smooth_zero (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 7 f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3] (s : Γ(E, ⊤))
    [SmoothOfRelativeDimension 4 ((zeroSchemeOfSection X E s).subschemeι ≫ f)] :
    letI := SmoothOfRelativeDimension.smooth 7 f
    IsRegularZeroSchemeSequence (fieldChowSituation K) f E s 3 4 := by
  let := SmoothOfRelativeDimension.smooth 7 f
  exact isRegularZeroSchemeSequence_of_smooth_zero K f 3 4 (fieldChowSituation K) f E s 4

end M9Native.SmoothZeroRegularity

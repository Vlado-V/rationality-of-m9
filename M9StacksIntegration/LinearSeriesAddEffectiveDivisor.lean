module

public import M9StacksIntegration.InvertibleHomCancellation
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.DegreeSurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionRegular

/-!
# Adding an actual effective divisor to a linear series

The regular canonical section of `O(D)` gives an actual monomorphism
`L → O(D) ⊗ L`. Its original map on zeroth cohomology is injective, so it
carries a linear series to a series of the same dimension and increased
degree. Over an algebraically closed field a smooth proper curve has an
actual point divisor P. The divisor 3P has degree three, and adding it to
a degree-two pencil constructs a native degree-five pencil.

The point construction follows the original closed-point argument in the
pinned native `Picard/TorsionSmoothProjectiveCurve/DegreeSurjective.lean`.
No effective divisor or positive-degree section is supplied as curve data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9StacksIntegration.LinearSeriesAddEffectiveDivisor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Divisors (IsEffectiveCartierDivisor)
open InvertibleHomCancellation (tensorRight)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k))
variable (hdim : topologicalKrullDim X ≤ 1)

/-- Monicity of an actual sheaf-module map gives injectivity of its native
map on zeroth cohomology. -/
theorem injective_cohomology_zero_of_mono {L M : X.Modules} (j : L ⟶ M) [Mono j] :
    Function.Injective (cohomologyOverFieldMap k f j 0) := by
  let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel j }
  obtain ⟨_δ, hinj, _⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact hinj

variable [IsProper f]

/-- The actual canonical section of an effective Cartier divisor embeds a
line bundle in its twist, with no new section or nonvanishing premise. -/
def divisorTwistInclusion (D : X.IdealSheafData) (L : X.Modules) :
    L ⟶ Scheme.Modules.tensorObj (Stacks.Divisors.invertibleSheaf' D) L :=
  (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
    X.ringCatSheaf.2 L).inv ≫ (tensorRight L).map (Stacks.Divisors.canonicalHom D)

theorem divisorTwistInclusion_mono (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Mono (divisorTwistInclusion D L) := by
  let : Mono (Stacks.Divisors.canonicalHom D) := Stacks.Divisors.canonicalSection_isRegular D
  let : (tensorRight L).IsEquivalence :=
    Scheme.Modules.isEquivalence_invertibleTensorRightFunctor L
  dsimp only [divisorTwistInclusion]
  infer_instance

/-- Add an actual effective divisor to the original line bundle and map
the original section subspace along the actual injective cohomology map. -/
def addEffectiveDivisor {d r : ℕ} (s : LinearSeries k f hdim d r)
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (e : ℕ)
    (hD : invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) = (e : ℤ)) :
    LinearSeries k f hdim (d + e) r := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 s.L := s.isInvertible
  let N : X.Modules := Stacks.Divisors.invertibleSheaf' D
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.tensorObj N s.L) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 N s.L
  let j := divisorTwistInclusion D s.L
  let : Mono j := divisorTwistInclusion_mono D s.L
  let j0 := (cohomologyOverFieldMap k f j 0).hom
  have hj0 : Function.Injective j0 := injective_cohomology_zero_of_mono f j
  refine
    { L := Scheme.Modules.tensorObj N s.L
      isInvertible := inferInstance
      degree_eq := ?_
      V := s.V.map j0
      finrank_eq := ?_ }
  · calc
      invertibleCurveDegree k f hdim (Scheme.Modules.tensorObj N s.L) =
          invertibleCurveDegree k f hdim N + invertibleCurveDegree k f hdim s.L :=
        invertibleCurveDegree_tensorSheaf_eq_add k f hdim N s.L
      _ = (e : ℤ) + (d : ℤ) := congrArg₂ (· + ·) hD s.degree_eq
      _ = ((d + e : ℕ) : ℤ) := by push_cast; ring
  · exact (Submodule.equivMapOfInjective j0 hj0 s.V).finrank_eq.symm.trans s.finrank_eq

/-- A genuine closed point supplies an effective Cartier divisor of degree
one, including the original divisor sheaf. -/
theorem exists_effective_point_degree_one [IsAlgClosed k] [IsCurve k f] [Smooth f] :
    ∃ (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D),
      letI := hD
      invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) = 1 := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : Nonempty X := (inferInstance : IsIntegral X).nonempty
  obtain ⟨x, _hx, hxc⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  let D := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hxc⟩ : Closeds X)
  have hD : IsEffectiveCartierDivisor D :=
    ((smoothAt_closedPoint_tfae_of_isCurve_of_perfectField k f hxc).out 5 4).mp
      (InfinitesimalLifting.smoothAt_of_smooth f x)
  refine ⟨D, hD, ?_⟩
  let := hD
  have h1 := invertibleCurveDegree_invertibleSheaf_eq_finrank_cohomologyOverField_zero k f hdim D
  have h2 := finrank_cohomologyOverField_pullback_eq_one k f hxc
    (Scheme.unitModule X) (SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2)
  rw [finrank_cohomologyOverField_eq_of_iso k (D.subschemeι ≫ f)
    (Scheme.Modules.pullbackUnitIso D.subschemeι) 0] at h2
  exact h1.trans (by exact_mod_cast h2)

/-- The original divisor-sheaf degree is the degree of its actual Picard
class, for the fixed native degree homomorphism. -/
theorem divisor_degree_eq_picard_degree (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) =
      Stacks.Picard.ofSchemeDegree k f hdim (Stacks.Divisors.picardClass D) := by
  exact (Stacks.Picard.ofSchemeDegree_picardClass k f hdim
    (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)).symm

/-- The divisor `nP`, cut out by the `n`th power of the actual point ideal,
is an effective divisor of degree `n`, including `n = 0`. -/
theorem exists_effective_degree [IsAlgClosed k] [IsCurve k f] [Smooth f] (n : ℕ) :
    ∃ (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D),
      letI := hD
      invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) = (n : ℤ) := by
  obtain ⟨P, hP, hp⟩ := exists_effective_point_degree_one f hdim
  let := hP
  refine ⟨P ^ n, inferInstance, ?_⟩
  rw [divisor_degree_eq_picard_degree f hdim, Stacks.Divisors.picardClass_pow, map_zsmul,
    ← divisor_degree_eq_picard_degree f hdim P, hp]
  simp

/-- The divisor `3P` is an actual effective divisor of degree three. -/
theorem exists_effective_degree_three [IsAlgClosed k] [IsCurve k f] [Smooth f] :
    ∃ (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D),
      letI := hD
      invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) = 3 :=
  exists_effective_degree f hdim 3

/-- Degree monotonicity is witnessed by an actual effective divisor and
the actual injective map of section subspaces. -/
theorem nonempty_linearSeries_of_degree_le [IsAlgClosed k] [IsCurve k f] [Smooth f]
    {d e r : ℕ} (hs : Nonempty (LinearSeries k f hdim d r)) (hde : d ≤ e) :
    Nonempty (LinearSeries k f hdim e r) := by
  obtain ⟨s⟩ := hs
  obtain ⟨D, hD, hd⟩ := exists_effective_degree f hdim (e - d)
  let := hD
  have hsum : d + (e - d) = e := Nat.add_sub_of_le hde
  rw [← hsum]
  exact ⟨addEffectiveDivisor f hdim s D (e - d) hd⟩

/-- A native degree-two pencil yields a native degree-five pencil by
adding the actual effective divisor `3P`. -/
theorem nonempty_degree_five_pencil_of_degree_two [IsAlgClosed k] [IsCurve k f] [Smooth f]
    (hs : Nonempty (LinearSeries k f hdim 2 1)) :
    Nonempty (LinearSeries k f hdim 5 1) := by
  obtain ⟨s⟩ := hs
  obtain ⟨D, hD, hd⟩ := exists_effective_degree_three f hdim
  let := hD
  exact ⟨addEffectiveDivisor f hdim s D 3 hd⟩

/-- The actual nonpentagonal condition therefore supplies the absence of
a degree-two pencil required by the canonical separation proof. -/
theorem no_degree_two_pencil_of_no_degree_five [IsAlgClosed k] [IsCurve k f] [Smooth f]
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) :
    ¬ Nonempty (LinearSeries k f hdim 2 1) :=
  fun h2 => hnp (nonempty_degree_five_pencil_of_degree_two f hdim h2)

end M9StacksIntegration.LinearSeriesAddEffectiveDivisor

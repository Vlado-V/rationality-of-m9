module

public import M9StacksIntegration.MukaiPointTwistBounds
public import M9StacksIntegration.MukaiPencilDegreeBounds
public import M9StacksIntegration.MukaiBundleTensor
public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional

/-!
# Actual section bounds in the uniqueness argument

These helpers use the actual native dualizing sheaf and its actual
degree. Its invertibility and canonical degree formula are explicit
inputs in this layer; the public smooth-curve wrapper discharges them.
No section-bound premise is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiCanonicalTwistBounds

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
  (Stacks.Duality.dualizingSheafOverField f)]
variable (hcanonicalDegree : invertibleCurveDegree k f hdim
  (Stacks.Duality.dualizingSheafOverField f) = 2 * (genus f : ℤ) - 2)
include hcanonicalDegree

/-- The actual canonical residual line bundle. -/
abbrev residual (L : X.Modules) : X.Modules :=
  residualLine (Stacks.Duality.dualizingSheafOverField f) L

theorem residual_isInvertible (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (residual f L) := by
  exact residualLine_isInvertible _ L

/-- The degree of the literal residual follows from its actual tensor
cancellation isomorphism. -/
theorem residual_degree (hg : genus f = 9) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI := residual_isInvertible f hdim hcanonicalDegree L
    invertibleCurveDegree k f hdim (residual f L) =
      16 - invertibleCurveDegree k f hdim L := by
  letI := isIso_globalSections_of_isAlgClosed k f
  letI := residual_isInvertible f hdim hcanonicalDegree L
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensor L (residual f L)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2
      L (residual f L)
  have hprod := invertibleCurveDegree_tensorSheaf_eq_add k f hdim L (residual f L)
  change invertibleCurveDegree k f hdim (tensor L (residual f L)) =
    invertibleCurveDegree k f hdim L + invertibleCurveDegree k f hdim (residual f L) at hprod
  have hcancel := invertibleCurveDegree_eq_of_iso k f hdim
    (residualTensorIso (Stacks.Duality.dualizingSheafOverField f) L)
  change invertibleCurveDegree k f hdim (tensor L (residual f L)) =
    invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) at hcancel
  have hω := hcanonicalDegree
  rw [hg] at hω
  omega

include hdim in
/-- Native Serre duality identifies sections of the actual residual with
first cohomology of the actual original line bundle. -/
theorem residual_h0 (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Module.finrank k (cohomologyOverField k f (residual f L) 0) =
      Module.finrank k (cohomologyOverField k f L 1) := by
  letI := modulesLinearOverField k f
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  letI := finiteDimensional_cohomologyOverField_of_isProper k f L 1
  let e₁ := MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f L
    (Stacks.Duality.dualizingSheafOverField f)
  let e₂ := cohomologyOverFieldIso k f
    (Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank L
      (Stacks.Duality.dualizingSheafOverField f) 1).symm 0
  have heq : Module.finrank k (L ⟶ Stacks.Duality.dualizingSheafOverField f) =
      Module.finrank k (cohomologyOverField k f (residual f L) 0) :=
    (e₁.trans e₂.toLinearEquiv).finrank_eq
  rw [← heq, (Stacks.Duality.homDualizingSheafLinearEquiv f hdim L
    (isQuasicoherent_of_isCoherent _)).finrank_eq, Subspace.dual_finrank_eq]

/-- In genus nine, degree ten allows at most four sections under the
actual no-degree-five-pencil hypothesis. -/
theorem h0_le_four_of_degree_ten
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hd : invertibleCurveDegree k f hdim L = 10) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 4 := by
  letI := isIso_globalSections_of_isAlgClosed k f
  letI := residual_isInvertible f hdim hcanonicalDegree L
  have hR := residual_degree f hdim hcanonicalDegree hg L
  have hbound := MukaiTwistBounds.h0_le_two_of_degree_le_six f hdim hnp (residual f L) (by omega)
  have hSerre := residual_h0 f hdim hcanonicalDegree L
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim L
  rw [hg, hd] at hRR
  omega

/-- Degree twelve allows at most five sections: six sections would give
a degree-four residual with two sections, hence a degree-five pencil. -/
theorem h0_le_five_of_degree_twelve
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hd : invertibleCurveDegree k f hdim L = 12) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 5 := by
  letI := isIso_globalSections_of_isAlgClosed k f
  letI := residual_isInvertible f hdim hcanonicalDegree L
  have hR := residual_degree f hdim hcanonicalDegree hg L
  have hbound := MukaiTwistBounds.h0_le_one_of_degree_le_five f hdim hnp (residual f L) (by omega)
  have hSerre := residual_h0 f hdim hcanonicalDegree L
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim L
  rw [hg, hd] at hRR
  omega

/-- Adding an actual effective divisor raises the degree to ten and
injects the original sections. Thus the degree-ten bound applies to all
nonnegative degrees at most ten. Negative degree has no sections. -/
theorem h0_le_four_of_degree_le_ten
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hd : invertibleCurveDegree k f hdim L ≤ 10) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 4 := by
  by_cases hneg : invertibleCurveDegree k f hdim L < 0
  · letI := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_zero_of_invertibleCurveDegree_neg k f hdim L hneg)
    have hz : Module.finrank k (cohomologyOverField k f L 0) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega
  · have hnn : 0 ≤ invertibleCurveDegree k f hdim L := by omega
    let d := (invertibleCurveDegree k f hdim L).toNat
    have hd' : invertibleCurveDegree k f hdim L = (d : ℤ) :=
      (Int.toNat_of_nonneg hnn).symm
    obtain ⟨D, hD, hdegree⟩ :=
      M9StacksIntegration.LinearSeriesAddEffectiveDivisor.exists_effective_degree f hdim (10-d)
    letI := hD
    let N : X.Modules := Stacks.Divisors.invertibleSheaf' D
    letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N :=
      Stacks.Divisors.invertibleSheaf_isInvertible D
    letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Scheme.Modules.tensorObj N L) :=
      Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 N L
    have he : invertibleCurveDegree k f hdim (Scheme.Modules.tensorObj N L) = 10 := by
      have hadd := invertibleCurveDegree_tensorSheaf_eq_add k f hdim N L
      change invertibleCurveDegree k f hdim (Scheme.Modules.tensorObj N L) =
        invertibleCurveDegree k f hdim N + invertibleCurveDegree k f hdim L at hadd
      rw [hadd, hdegree, hd']
      have hle : d ≤ 10 := by omega
      omega
    let j := M9StacksIntegration.LinearSeriesAddEffectiveDivisor.divisorTwistInclusion D L
    letI : Mono j :=
      M9StacksIntegration.LinearSeriesAddEffectiveDivisor.divisorTwistInclusion_mono D L
    have hj : Function.Injective (cohomologyOverFieldMap k f j 0).hom :=
      M9StacksIntegration.LinearSeriesAddEffectiveDivisor.injective_cohomology_zero_of_mono f j
    have hb := h0_le_four_of_degree_ten f hdim hcanonicalDegree hg hnp (Scheme.Modules.tensorObj N L) he
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : (Scheme.Modules.tensorObj N L).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
    letI := finiteDimensional_cohomologyOverField_of_isProper k f (Scheme.Modules.tensorObj N L) 0
    have hr := LinearMap.finrank_range_of_inj hj
    have hl := (LinearMap.range (cohomologyOverFieldMap k f j 0).hom).finrank_le
    change Module.finrank k (LinearMap.range (cohomologyOverFieldMap k f j 0).hom) ≤
      Module.finrank k (cohomologyOverField k f (Scheme.Modules.tensorObj N L) 0) at hl
    omega

end M9Native.MukaiCanonicalTwistBounds

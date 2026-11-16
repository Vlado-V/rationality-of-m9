module

public import M9StacksIntegration.AllTestNativeFamilyOpenReduction
public import M9StacksIntegration.AllTestNativeSchemeGenusComparison
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyUnconditional

/-!
# Actual intrinsic native genus membership of EVERY original family

The existing native providers are source/object/trace verified in the current
readiness receipt. This new integration source needs its own direct and fresh
kernel checks before its declarations are a checked provider.

The actual unconditional native cohomology theorem discharges both H1
hypotheses of the genuine open-locus theorem. The intrinsic field-fibre
predicate is compared with actual cohomological genus using the proved
rank theorem. Actual schematic-cover descent then proves intrinsic M_g
membership of EVERY literal original family, including nonschematic totals.
No openness, membership, classifier, cohomology comparison or original
family-equivalence assertion is an argument to that theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeFamilyMembership
open AllTestBoundedCharts AllTestNativeCurveFamily
  AllTestNativeFamilyOpenReduction AllTestNativeSchemeGenusComparison
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Intrinsic native field-fibre genus equals the ACTUAL rank of R1, with
universal H0 as native geometric data rather than a comparison premise. -/
theorem intrinsic_iff_cohomological (g : ℕ) (F : CurveFamily B hZ) :
    IsSmoothH0FamilyOfFibreGenus B hZ g F ↔
      IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g :=
  and_congr_right fun hF =>
    F.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
      (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hF.2) g

/-- The actual unconditional native H1 theorem proves the intrinsic M_g
open locus; openness is NOT an input. -/
theorem intrinsic_isOpen (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsSmoothH0FamilyOfFibreGenus B hZ g) :=
  (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2).of_iff
      (fun F => (intrinsic_iff_cohomological B hZ g F).symm)

/-- The genuine native image of EVERY literal original family belongs to
intrinsic native M_g. The total need not be schematic; the genus condition
on the original family still quantifies over ALL original extension fields. -/
theorem nativeCurveFamily_membership
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    IsSmoothH0FamilyOfFibreGenus B hZ g (nativeCurveFamily B hZ K hK F) :=
  nativeFamily_property_of_schematic B hZ K hK (intrinsic_isOpen B hZ g) g
    (fun q hq => nativeSchemeFamily_membership B hZ K hK q g hq) F

end M9StacksIntegration.AllTestNativeFamilyMembership

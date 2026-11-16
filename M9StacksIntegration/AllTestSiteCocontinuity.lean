module

public import M9StacksIntegration.AllTestBoundedRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Actual fppf cocontinuity into the full original test category

The native standard-cover theorem refines EVERY original fppf covering of
a contained scheme by a chosen covering of the native site. Applied to the
actual covering-sieve criterion, it proves fppf cocontinuity; the slice
comparison follows from the genuine Over.post cocontinuity theorem.
No cover-lifting, site equivalence or classification premise is supplied.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace M9StacksIntegration.AllTestSiteCocontinuity
open AllTestBoundedCharts AllTestBoundedRestriction
universe u

/-- Actual fppf cocontinuity, using the proved standard fppf refinement. -/
theorem inclusion_isCocontinuous_fppf (B : BigFppfSite.{u}) :
    B.inclusion.IsCocontinuous B.topology Scheme.fppfTopology := by
  classical
  let : Scheme.fppfPrecoverage.HasIsos := ⟨by
    intro X Y f hf
    let : IsIso f := hf
    exact f.singleton_mem_fppfPrecoverage⟩
  constructor
  intro T R hR
  rw [Scheme.fppfTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨P, hP, hPR⟩ := hR
  obtain ⟨E, rfl⟩ := P.exists_eq_preZeroHypercover
  obtain ⟨V, hV, ⟨φ⟩⟩ := exists_isCovering_refining_fppfCovering B T E hP
  apply B.topology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck
      (show V.presieve₀ ∈ B.precoverage T from ⟨V, rfl, hV⟩))
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  change R (B.inclusion.map (V.f i))
  have hw : φ.h₀ i ≫ E.f (φ.s₀ i) = B.inclusion.map (V.f i) := φ.w₀ i
  rw [← hw]
  exact R.downward_closed (hPR _ _ ⟨φ.s₀ i⟩) (φ.h₀ i)

/-- Every original fppf covering sieve of a bounded ORIGINAL test restricts
to a genuine native fppf covering sieve; the original coefficient map stays
literal. This is proved rather than assumed as a site comparison. -/
theorem boundedInclusion_isCocontinuous (K : Type u) [Field K]
    (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))) :
    (boundedInclusion B K hK).IsCocontinuous
      (BigFppfOver.topology B (Spec (.of K)) hK)
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) := by
  let : B.inclusion.IsCocontinuous B.topology Scheme.fppfTopology :=
    inclusion_isCocontinuous_fppf B
  change (Over.post (X := B.obj hK) B.inclusion).IsCocontinuous
    (B.topology.over (B.obj hK)) (Scheme.fppfTopology.over (B.inclusion.obj (B.obj hK)))
  infer_instance

end M9StacksIntegration.AllTestSiteCocontinuity

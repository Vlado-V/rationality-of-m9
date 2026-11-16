module

public import M9StacksIntegration.AllTestSchemeCurveConstants
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Canonical residue fibres imply the FULL original all-field curve condition

Every original field-valued point factors through its actual residue field,
with its ORIGINAL scalar homomorphism. Actual Cartesian cancellation and
proved original curve base change carry the residue-fibre condition to the
entire original field fibre. This derives, rather than replaces, the original
quantification over ALL extension fields, including fields outside a native
cutoff. No family-classifier or cohomology/rank comparison is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestResidueSchemeCurve
open StandaloneCurveCohomology
universe u

/-- Original residue-field curves give the literal original all-field
SchemeCurve condition, using actual field-point factorization and pullbacks. -/
theorem schemeCurve_of_residue_fibres {Z T : Scheme.{u}} (q : Z ⟶ T)
    [IsProper q] [SmoothOfRelativeDimension 1 q] (g : ℕ)
    (hres : ∀ t : T, M9StandaloneDraft.SchemeCurve (q.fiberToSpecResidueField t) g) :
    M9StandaloneDraft.SchemeCurve q g := by
  have hgc : GeometricallyConnected q :=
    (GeometricallyConnected.iff_geometricallyConnected_fiber (f := q)).mpr
      (fun t => (hres t).2.2.1)
  refine ⟨inferInstance, inferInstance, hgc, ?_⟩
  intro L _ s
  let t : T := s (IsLocalRing.closedPoint L)
  let a : Spec (.of L) ⟶ Spec (T.residueField t) :=
    Spec.map (T.descResidueField (Scheme.stalkClosedPointTo s))
  have hfac : a ≫ T.fromSpecResidueField t = s :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L T s
  have hbig : IsPullback (pullback.fst q s) (pullback.snd q s) q
      (a ≫ T.fromSpecResidueField t) := by
    rw [hfac]
    exact IsPullback.of_hasPullback q s
  have hright : IsPullback (q.fiberι t) (q.fiberToSpecResidueField t) q
      (T.fromSpecResidueField t) := IsPullback.of_hasPullback q _
  have hleft := hbig.of_right' hright
  have hL := schemeCurve_of_isPullback (q.fiberToSpecResidueField t)
    (pullback.snd q s) _ a hleft (hres t)
  refine ⟨finite_standalone_H1 (pullback.snd q s), ?_⟩
  change genus (pullback.snd q s) = g
  exact AllTestNativeSchematicCharts.genus_eq_of_schemeCurve _ hL

/-- This is an actual equivalence of the FULL original predicate, not a
weakened replacement involving only selected native field points. -/
theorem schemeCurve_iff_residue_fibres {Z T : Scheme.{u}} (q : Z ⟶ T)
    [IsProper q] [SmoothOfRelativeDimension 1 q] (g : ℕ) :
    M9StandaloneDraft.SchemeCurve q g ↔
      ∀ t : T, M9StandaloneDraft.SchemeCurve (q.fiberToSpecResidueField t) g := by
  refine ⟨fun h t => ?_, schemeCurve_of_residue_fibres q g⟩
  exact schemeCurve_of_isPullback q (q.fiberToSpecResidueField t) (q.fiberι t)
    (T.fromSpecResidueField t) (IsPullback.of_hasPullback q _) h

end M9StacksIntegration.AllTestResidueSchemeCurve

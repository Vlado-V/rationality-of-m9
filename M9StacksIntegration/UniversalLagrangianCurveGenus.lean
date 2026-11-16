module

public import M9StacksIntegration.SmoothFamilyCurveCondition
public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth

/-!
# The original universal family's all-field genus condition

The base is the original canonical good open in the actual irreducible
Grassmannian. Properness and smooth relative dimension one have already
been proved for the original restricted projection. Once its genuine
geometric connectedness is supplied by the connectedness construction,
the genus of any actual fibre is the genus on every original field
fibre, with actual finite H1. This leaf does not assert that the genus
is nine or supply connectedness as a new axiom.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.UniversalLagrangianCurveGenus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open M9Native.LagrangianLinearSections M9Native.LagrangianLinearSectionGenericSmooth

/-- The literal original family satisfies the all-field curve condition
with the native genus computed at an actual field fibre. Preconnectedness
of its original base, finiteness of every H1 and all genus comparisons
are proved here. Geometric connectedness remains the independent
geometric input, rather than a genus or family-class premise. -/
theorem schemeCurve_of_geometricallyConnected
    (K : Type u) [Field K] [CharZero K]
    [GeometricallyConnected (restrictedProjection K)]
    {L : Type u} [Field L] (p : Spec (.of L) ⟶ (goodOpen K).toScheme) :
    M9StandaloneDraft.SchemeCurve (restrictedProjection K)
      (genus (pullback.snd (restrictedProjection K) p)) := by
  let : PreirreducibleSpace (goodOpen K).toScheme :=
    (goodOpen K).ι.isOpenEmbedding.preirreducibleSpace
  exact SmoothFamilyCurveCondition.schemeCurve_of_isPullback (restrictedProjection K) p
    (pullback.fst (restrictedProjection K) p) (pullback.snd (restrictedProjection K) p)
    (IsPullback.of_hasPullback (restrictedProjection K) p)

end M9Native.UniversalLagrangianCurveGenus

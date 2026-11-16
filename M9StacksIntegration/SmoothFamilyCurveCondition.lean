module

public import M9StacksIntegration.Private.SmoothFamilyGenusConstant
public import M9StacksIntegration.StandaloneCurveCohomology

/-!
# The original all-field curve condition from a smooth geometric family

The genus in the conclusion is the native genus of an actual chosen
Cartesian field fibre. Properness proves the finiteness of every original
H1, and the actual derived-fibre Euler theorem proves its dimension is
the same on every field-valued fibre. No genus or family-class premise
occurs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.SmoothFamilyCurveCondition
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- A proper smooth geometrically connected relative curve on a
preconnected base satisfies the literal original all-field curve
condition, with genus computed from any actual field fibre. -/
theorem schemeCurve_of_isPullback
    {S Y : Scheme.{u}} [PreconnectedSpace S] (p : Y ⟶ S) [IsProper p]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ S)
    {Z : Scheme.{u}} (q : Z ⟶ Y) (g : Z ⟶ Spec (.of K))
    (sq : IsPullback q g p x) : M9StandaloneDraft.SchemeCurve p (genus g) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro L _ s
  refine ⟨M9StacksIntegration.StandaloneCurveCohomology.finite_standalone_H1 _, ?_⟩
  change genus (pullback.snd p s) = genus g
  exact SmoothFamilyGenusConstant.genus_eq_of_isPullback p s x
    (pullback.fst p s) (pullback.snd p s) (IsPullback.of_hasPullback p s) q g sq

end M9Native.SmoothFamilyCurveCondition

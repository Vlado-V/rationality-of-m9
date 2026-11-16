module

public import M9StacksIntegration.StandaloneCurveCohomology
public import M9StacksIntegration.AllTestNativeSchematicCharts
public import M9StacksIntegration.SmoothConnectedCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Actual constant functions on every original scheme-curve fibre

The original proper smooth geometrically connected condition proves that
the canonical homomorphism from the ORIGINAL coefficient field to the
actual global functions is an isomorphism. Every arbitrary field-valued
base change has the same property. No H0, finrank-H0, geometric integrality,
or universal base-change premise is supplied.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestSchemeCurveConstants
open StandaloneCurveCohomology
universe u

/-- Actual canonical H0 constants over the original field, from the original
geometric curve predicate. -/
theorem isIso_constants_of_schemeCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {g : ℕ} (hq : M9StandaloneDraft.SchemeCurve f g) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  let : IsProper f := hq.1
  let : SmoothOfRelativeDimension 1 f := hq.2.1
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : GeometricallyConnected f := hq.2.2.1
  let : GeometricallyReduced f := geometricallyReduced_of_smooth f
  exact Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper k f

/-- The genuine constants map is an isomorphism on EVERY original
field-valued fibre, with its exact original structural field action. -/
theorem isIso_constants_on_every_field_fibre {Z T : Scheme.{u}} (q : Z ⟶ T)
    {g : ℕ} (hq : M9StandaloneDraft.SchemeCurve q g)
    (L : Type u) [Field L] (s : Spec (.of L) ⟶ T) :
    IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ (pullback.snd q s).appTop) :=
  isIso_constants_of_schemeCurve (pullback.snd q s)
    (schemeCurve_of_isPullback q (pullback.snd q s) (pullback.fst q s) s
      (IsPullback.of_hasPullback q s) hq)

/-- The original field fibre is an ACTUAL native integral curve of dimension
one, with canonical constants and original cohomological genus. None of
these conclusions is supplied as a premise. -/
theorem schemeCurve_field_geometry {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {g : ℕ} (hq : M9StandaloneDraft.SchemeCurve f g) :
    IsCurve k f ∧ topologicalKrullDim X = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = g := by
  let : IsProper f := hq.1
  let : SmoothOfRelativeDimension 1 f := hq.2.1
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : GeometricallyConnected f := hq.2.2.1
  let : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton (f := f)
  let : IsIntegral X := M9Native.SmoothConnectedCurve.isIntegral_of_smooth_connected f
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1
  exact ⟨M9Native.SmoothConnectedCurve.isCurve_of_smooth_geometricallyConnected f hdim,
    hdim, isIso_constants_of_schemeCurve f hq,
    AllTestNativeSchematicCharts.genus_eq_of_schemeCurve f hq⟩

/-- All these genuine curve and cohomology conclusions hold on EVERY original
field-valued base change, including nonclosed fields and arbitrary extensions. -/
theorem schemeCurve_every_field_fibre_geometry {Z T : Scheme.{u}} (q : Z ⟶ T)
    {g : ℕ} (hq : M9StandaloneDraft.SchemeCurve q g)
    (L : Type u) [Field L] (s : Spec (.of L) ⟶ T) :
    IsCurve L (pullback.snd q s) ∧ topologicalKrullDim (pullback q s : Scheme.{u}) = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ (pullback.snd q s).appTop) ∧
      genus (pullback.snd q s) = g :=
  schemeCurve_field_geometry (pullback.snd q s)
    (schemeCurve_of_isPullback q (pullback.snd q s) (pullback.fst q s) s
      (IsPullback.of_hasPullback q s) hq)

/-- Conversely, the actual native field geometry gives the entire original
all-field-point condition. The structural map of an arbitrary field-valued
point supplies its exact original algebra structure, rather than a chosen
field isomorphism. -/
theorem schemeCurve_of_native_field_geometry {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hsm : Smooth f)
    (hdim : topologicalKrullDim X = 1)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
    {g : ℕ} (hgen : genus f = g) : M9StandaloneDraft.SchemeCurve f g := by
  let : Smooth f := hsm
  let : GeometricallyReduced f := geometricallyReduced_of_smooth f
  let : GeometricallyConnected f := (isIso_globalSections_iff_geometricallyConnected k f).1 hH0
  let : IsCurve k f := M9Native.SmoothConnectedCurve.isCurve_of_smooth_geometricallyConnected f hdim
  refine ⟨inferInstance, smoothOfRelativeDimension_one_of_isCurve k f, inferInstance, ?_⟩
  intro L _ s
  let : Algebra k L := (Spec.preimage s).hom.toAlgebra
  have hs : Spec.map (CommRingCat.ofHom (algebraMap k L)) = s := Spec.map_preimage s
  have hsq : IsPullback (pullback.fst f s) (pullback.snd f s) f
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [hs]
    exact IsPullback.of_hasPullback f s
  exact ⟨finite_standalone_H1 (pullback.snd f s), (genus_baseChange k L _ _ f hsq).trans hgen⟩

/-- Literal equivalence of the original all-test scheme-curve condition and
the actual native point geometry over the SAME original field and map. -/
theorem schemeCurve_iff_native_field_geometry {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : ℕ) :
    M9StandaloneDraft.SchemeCurve f g ↔
      IsProper f ∧ Smooth f ∧ topologicalKrullDim X = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = g := by
  constructor
  · intro h
    let : SmoothOfRelativeDimension 1 f := h.2.1
    exact ⟨h.1, SmoothOfRelativeDimension.smooth 1 f, (schemeCurve_field_geometry f h).2⟩
  · rintro ⟨hp, hs, hd, hc, hg⟩
    let : IsProper f := hp
    exact schemeCurve_of_native_field_geometry f hs hd hc hg

end M9StacksIntegration.AllTestSchemeCurveConstants

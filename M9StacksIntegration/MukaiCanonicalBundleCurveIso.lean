module

public import M9StacksIntegration.MukaiCanonicalBundleIsoTransport
public import M9StacksIntegration.GenusNineMukaiBundle

/-!
# The canonical Mukai bundles on two isomorphic original curves

Actual pullback transports the complete canonical generated
semi-irreducible property. The genuine degree-eight-net theorem and
bundle uniqueness on the source curve then construct an isomorphism
from its original bundle to the pulled-back target bundle. No net,
bundle isomorphism, section comparison or polarization is assumed.

This comparison is conditional on the actual bundle properties on the
two curves; it does not establish those properties for a reverse
universal quotient or assert a parameter-orbit converse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiCanonicalBundleCurveIso

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsProper f] [IsCurve k f] [Smooth f]
  [IsProper g] [IsCurve k g] [Smooth g]
  (e : X ≅ Y) (he : e.hom ≫ g = f)

include he in
/-- The genuine net-free uniqueness theorem constructs the actual
bundle isomorphism on the source of the original over-field curve
isomorphism. -/
theorem canonical_generated_semi_bundles_iso_over_curveIso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le 5 1))
    (EC : X.Modules) (ED : Y.Modules)
    (hEC : MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f EC)
    (hED : MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi g ED) :
    Nonempty (EC ≅ (Scheme.Modules.pullback e.hom).obj ED) := by
  have hED' := MukaiCanonicalBundleIsoTransport.isCanonicalGeneratedSemi_pullback
    k f g e he ED hED
  obtain ⟨E₀, _, unique⟩ :=
    GenusNineMukaiBundle.exists_unique_canonical_generated_semi k f hg hnp
  obtain ⟨a⟩ := unique EC hEC
  obtain ⟨b⟩ := unique ((Scheme.Modules.pullback e.hom).obj ED) hED'
  exact ⟨a.symm ≪≫ b⟩

include he in
/-- Both the actual pulled-back canonical property and the resulting
actual bundle comparison are available together for the same original
curve isomorphism. -/
theorem canonical_properties_on_two_curves
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le 5 1))
    (EC : X.Modules) (ED : Y.Modules)
    (hEC : MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f EC)
    (hED : MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi g ED) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f
        ((Scheme.Modules.pullback e.hom).obj ED) ∧
      Nonempty (EC ≅ (Scheme.Modules.pullback e.hom).obj ED) :=
  ⟨MukaiCanonicalBundleIsoTransport.isCanonicalGeneratedSemi_pullback k f g e he ED hED,
    canonical_generated_semi_bundles_iso_over_curveIso
      k f g e he hg hnp EC ED hEC hED⟩

end M9Native.MukaiCanonicalBundleCurveIso

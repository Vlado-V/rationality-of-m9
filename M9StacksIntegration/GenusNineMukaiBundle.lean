module

public import M9StacksIntegration.DirectC9DegreeEightNet
public import M9StacksIntegration.MukaiCanonicalBundleOnSmoothCurve

/-!
# The original canonical Mukai bundle in genus nine

The actual Brill--Noether theorem constructs the degree-eight net.
The residual-net construction then gives the original canonical,
generated, completely semi-irreducible rank-three bundle, unique up to
an actual isomorphism. No net, line, section basis or bundle is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u
namespace M9Native.GenusNineMukaiBundle

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] [Smooth f]

/-- The actual original curve has a degree-eight net; the C9 parameter
space and its incidence classes have been eliminated from the conclusion. -/
theorem nonempty_degree_eight_net (hg : genus f = 9) :
    Nonempty (LinearSeries k f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le 8 2) := by
  letI : IsCurve k (Over.mk f).hom := (inferInstance : IsCurve k f)
  letI : IsProper (Over.mk f).hom := (inferInstance : IsProper f)
  letI : Smooth (Over.mk f).hom := (inferInstance : Smooth f)
  exact DirectC9DegreeEightNet.nonempty_degree_eight_net k (Over.mk f) hg

/-- Every original smooth proper nonpentagonal genus-nine curve has its
canonical Mukai bundle, unique among bundles with the actual complete
system properties. All Brill--Noether and canonical-line inputs are derived. -/
theorem exists_unique_canonical_generated_semi [CharZero k]
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le 5 1)) :
    ∃ E : X.Modules,
      MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f E ∧
      ∀ F : X.Modules,
        MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f F → Nonempty (E ≅ F) :=
  MukaiCanonicalBundleOnSmoothCurve.exists_unique_up_to_iso_of_net_exists f hg hnp
    (nonempty_degree_eight_net k f hg)

end M9Native.GenusNineMukaiBundle

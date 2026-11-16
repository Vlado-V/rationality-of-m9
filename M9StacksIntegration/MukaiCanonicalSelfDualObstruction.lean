module

public import M9StacksIntegration.MukaiTwistedSelfDualObstruction
public import M9StacksIntegration.MukaiCanonicalExteriorDegree

/-!
# The twisted self-duality obstruction for a canonical genus-nine bundle

The native top-exterior canonical isomorphism gives degree sixteen by
the checked canonical-degree calculation. The actual all-field-fiber
isomorphism assumption is then contradicted by the checked integral
degree obstruction. The determinant degree is derived, not an input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiCanonicalExteriorCohomology
open M9Native.MukaiTwistedSelfDualObstruction

universe u

namespace M9Native.MukaiCanonicalSelfDualObstruction

variable {X : Scheme.{u}} (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hg : genus f = 9)

include k f hdim d hg

/-- The actual canonical determinant rules out every actual twisted
self-duality on a regular genus-nine curve. -/
theorem no_twistedSelfDualIso (hreg : IsRegular X) (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (e : twistedDual ξ E ≅ E) : False :=
  no_iso_rankThree_degreeSixteen k f hdim hreg ξ E
    (canonical_curveDegree_genus_nine k f hdim E d hg) e

/-- On the original smooth genus-nine curve no map from an actual
twisted dual is invertible on all actual field fibers. -/
theorem not_fieldFiberIsomorphisms [Smooth f] (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (a : twistedDual ξ E ⟶ E) : ¬ FieldFiberIsomorphisms a :=
  not_fieldFiberIsomorphisms_on_smooth_curve k f hdim ξ E
    (canonical_curveDegree_genus_nine k f hdim E d hg) a

end M9Native.MukaiCanonicalSelfDualObstruction

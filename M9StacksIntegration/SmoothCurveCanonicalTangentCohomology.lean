module

public import M9StacksIntegration.CurveCanonicalTangentCohomology
public import M9StacksIntegration.Private.CurveCanonicalInvertibility

/-!
# Unconditional dual-canonical cohomology for smooth proper genus-nine curves

The actual smooth-curve normalized-dualizing model supplies canonical
invertibility. The original canonical dual-line calculation therefore
has no extra invertibility input. Native canonical degree, evaluation,
negative degree and line Riemann--Roch derive the original H0/H1 values.
No rank-three bundle, determinant isomorphism, degree, cohomology count,
or deformation-space dimension is assumed.

Comparison with the original tangent sheaf `(Ω_{X/k})^∨` and passage to
moduli-space dimension remain separate genuine geometry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open M9Native.CurveCanonicalTangentCohomology

universe u

namespace M9Native.SmoothCurveCanonicalTangentCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hg : genus f = 9)

include hg

/-- Original dual-canonical H0 vanishes, with canonical invertibility derived from smoothness. -/
theorem canonicalTangent_h0_subsingleton :
    Subsingleton (cohomologyOverField k f (canonicalTangent f) 0) := by
  let := CurveCanonicalInvertibility.dualizing_isInvertible f
  exact CurveCanonicalTangentCohomology.canonicalTangent_h0_subsingleton_genus_nine f hg

/-- The actual original dual-canonical H0 dimension is zero. -/
theorem canonicalTangent_h0 :
    Module.finrank k (cohomologyOverField k f (canonicalTangent f) 0) = 0 := by
  let := CurveCanonicalInvertibility.dualizing_isInvertible f
  exact CurveCanonicalTangentCohomology.canonicalTangent_h0_genus_nine f hg

/-- The actual original dual-canonical H1 dimension is twenty-four. -/
theorem canonicalTangent_h1 :
    Module.finrank k (cohomologyOverField k f (canonicalTangent f) 1) = 24 := by
  let := CurveCanonicalInvertibility.dualizing_isInvertible f
  exact CurveCanonicalTangentCohomology.canonicalTangent_h1_genus_nine f hg

/-- Both original numerical invariants, from only the actual smooth proper genus-nine curve. -/
theorem canonicalTangent_h0_h1 :
    Module.finrank k (cohomologyOverField k f (canonicalTangent f) 0) = 0 ∧
      Module.finrank k (cohomologyOverField k f (canonicalTangent f) 1) = 24 :=
  ⟨canonicalTangent_h0 f hg, canonicalTangent_h1 f hg⟩

end M9Native.SmoothCurveCanonicalTangentCohomology

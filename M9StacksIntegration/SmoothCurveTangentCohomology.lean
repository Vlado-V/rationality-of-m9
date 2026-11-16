module

public import M9StacksIntegration.SmoothCurveCanonicalDifferentials
public import M9StacksIntegration.SmoothCurveCanonicalTangentCohomology
public import M9StacksIntegration.CurveTangentLineGeometry

/-!
# The actual tangent cohomology of an original smooth genus-nine curve

The actual native canonical/cotangent isomorphism gives an actual dual
isomorphism, preserving the original field action on cohomology. The
checked dual-canonical calculation then gives H0=0 and H1=24 for the
literal native tangent sheaf. No comparison, degree, cohomology count,
rank-three bundle, determinant or moduli dimension is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.CurveTangentLineGeometry M9Native.CurveCanonicalTangentCohomology

universe u

namespace M9Native.SmoothCurveTangentCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The literal original tangent line is the literal original canonical dual,
through genuine native duality and the actual sheaf dual functor. -/
def tangentCanonicalIso : tangentLine f ≅ canonicalTangent f :=
  dualSheafIsoOfIso (SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso f)

/-- Actual base-field scalar-compatible cohomology transport in every degree. -/
def tangentCanonicalCohomologyEquiv (n : ℕ) :
    cohomologyOverField k f (tangentLine f) n ≃ₗ[k]
      cohomologyOverField k f (canonicalTangent f) n :=
  (cohomologyOverFieldIso k f (tangentCanonicalIso f) n).toLinearEquiv

variable [IsAlgClosed k] (hg : genus f = 9)

include hg

/-- Actual global tangent fields vanish. -/
theorem tangent_h0_subsingleton :
    Subsingleton (cohomologyOverField k f (tangentLine f) 0) := by
  let := SmoothCurveCanonicalTangentCohomology.canonicalTangent_h0_subsingleton f hg
  exact ⟨fun x y => (tangentCanonicalCohomologyEquiv f 0).injective (Subsingleton.elim _ _)⟩

/-- Actual tangent H0 has dimension zero. -/
theorem tangent_h0 : Module.finrank k (cohomologyOverField k f (tangentLine f) 0) = 0 := by
  let := tangent_h0_subsingleton f hg
  exact Module.finrank_zero_of_subsingleton

/-- Actual tangent H1 has dimension twenty-four. -/
theorem tangent_h1 : Module.finrank k (cohomologyOverField k f (tangentLine f) 1) = 24 := by
  exact (tangentCanonicalCohomologyEquiv f 1).finrank_eq.trans
    (SmoothCurveCanonicalTangentCohomology.canonicalTangent_h1 f hg)

/-- Original smooth proper genus-nine curves supply both actual tangent dimensions. -/
theorem tangent_h0_h1 :
    Module.finrank k (cohomologyOverField k f (tangentLine f) 0) = 0 ∧
      Module.finrank k (cohomologyOverField k f (tangentLine f) 1) = 24 :=
  ⟨tangent_h0 f hg, tangent_h1 f hg⟩

end M9Native.SmoothCurveTangentCohomology

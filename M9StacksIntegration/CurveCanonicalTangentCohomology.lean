module

public import M9StacksIntegration.CanonicalLineCohomology
public import M9StacksIntegration.MukaiDualDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# Actual cohomology of the dual canonical line in genus nine

The canonical line is the literal native dualizing sheaf, and its dual
is the literal native sheaf dual. True canonical invertibility is the
independent smooth-curve model provider's output. Native canonical
cohomology computes its degree; actual evaluation and tensor degree
compute the dual degree; negative degree kills H0; line Riemann--Roch
then gives H1 dimension twenty-four.

No degree, H0 value, H1 value, deformation-space dimension, or rank-three
bundle is supplied. Identification with the actual derivation/tangent
sheaf requires the genuine native smooth-curve differentials--dualizing
comparison and is not inferred from these numbers alone.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.CurveCanonicalTangentCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]

/-- The literal dual of the actual native canonical sheaf. -/
abbrev canonicalTangent : X.Modules := dualSheaf (Stacks.Duality.dualizingSheafOverField f)

variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
  (Stacks.Duality.dualizingSheafOverField f)]

omit [IsAlgClosed k] [IsCurve k f] in
/-- Actual native duality preserves invertibility of this canonical line. -/
theorem canonicalTangent_isInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (canonicalTangent f) := by
  let hω := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X
    (Stacks.Duality.dualizingSheafOverField f)
  have hT := isFiniteLocallyFreeOfRank_dualSheaf (Stacks.Duality.dualizingSheafOverField f) 1 hω
  exact (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
    X (canonicalTangent f)).mpr hT

variable (hdim : topologicalKrullDim X ≤ 1)

/-- True canonical degree and the actual evaluation tensor pairing
derive the dual canonical degree, with no degree premise. -/
theorem canonicalTangent_degree :
    letI := canonicalTangent_isInvertible f
    invertibleCurveDegree k f hdim (canonicalTangent f) = 2 - 2 * (genus f : ℤ) := by
  let := canonicalTangent_isInvertible f
  let hω := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X
    (Stacks.Duality.dualizingSheafOverField f)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Duality.dualizingSheafOverField f) 1 := hω
  let := isFiniteLocallyFreeOfRank_dualSheaf (Stacks.Duality.dualizingSheafOverField f) 1 hω
  let := isIso_globalSections_of_isAlgClosed k f
  have hdual := MukaiDualDegree.curveDegree_dual_line k f hdim
    (Stacks.Duality.dualizingSheafOverField f) hω
  have hωdegree := CanonicalLineCohomology.canonical_degree f hdim
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim (canonicalTangent f),
    ← invertibleCurveDegree_eq_curveDegree k f hdim
      (Stacks.Duality.dualizingSheafOverField f)] at hdual
  linarith

theorem canonicalTangent_degree_genus_nine (hg : genus f = 9) :
    letI := canonicalTangent_isInvertible f
    invertibleCurveDegree k f hdim (canonicalTangent f) = -16 := by
  have h := canonicalTangent_degree f hdim
  rw [hg] at h
  norm_num at h
  exact h

/-- Negative actual degree proves vanishing of the original native H0,
not merely the finrank of a replacement vector space. -/
theorem canonicalTangent_h0_subsingleton_genus_nine (hg : genus f = 9) :
    Subsingleton (cohomologyOverField k f (canonicalTangent f) 0) := by
  let hdim := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  let := canonicalTangent_isInvertible f
  have hneg : invertibleCurveDegree k f hdim (canonicalTangent f) < 0 := by
    rw [canonicalTangent_degree_genus_nine f hdim hg]
    norm_num
  exact ModuleCat.subsingleton_of_isZero
    (isZero_cohomologyOverField_zero_of_invertibleCurveDegree_neg k f hdim
      (canonicalTangent f) hneg)

theorem canonicalTangent_h0_genus_nine (hg : genus f = 9) :
    Module.finrank k (cohomologyOverField k f (canonicalTangent f) 0) = 0 := by
  let := canonicalTangent_h0_subsingleton_genus_nine f hg
  exact Module.finrank_zero_of_subsingleton

/-- Actual line Riemann--Roch computes the original H1 dimension from
the derived degree and the actual H0 vanishing. -/
theorem canonicalTangent_h1_genus_nine (hg : genus f = 9) :
    Module.finrank k (cohomologyOverField k f (canonicalTangent f) 1) = 24 := by
  let hdim := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  let := canonicalTangent_isInvertible f
  let := isIso_globalSections_of_isAlgClosed k f
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim (canonicalTangent f)
  rw [canonicalTangent_h0_genus_nine f hg,
    canonicalTangent_degree_genus_nine f hdim hg, hg] at h
  omega

/-- The numerical canonical-tangent input to deformation theory. This
is not itself a moduli-space dimension theorem. -/
theorem canonicalTangent_h0_h1_genus_nine (hg : genus f = 9) :
    Module.finrank k (cohomologyOverField k f (canonicalTangent f) 0) = 0 ∧
      Module.finrank k (cohomologyOverField k f (canonicalTangent f) 1) = 24 :=
  ⟨canonicalTangent_h0_genus_nine f hg, canonicalTangent_h1_genus_nine f hg⟩

end M9Native.CurveCanonicalTangentCohomology

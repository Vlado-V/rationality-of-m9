module

public import M9StacksIntegration.GenusNineDualizingModel

/-! The original tricanonical bundle of every smooth proper genus-nine curve:
degree forty-eight, forty sections, and vanishing first cohomology. The ground
field is arbitrary; the original constant-global-functions condition is retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Duality (dualizingSheafOverField)
universe u
namespace M9Native.GenusNineTricanonicalCohomology
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The literal third tensor power of the actual original dualizing sheaf. -/
def tricanonical : X.Modules :=
  letI := GenusNineDualizingModel.dualizing_isInvertible f
  CanonicalHilbertFunction.canonicalPower f 3

instance tricanonical_isInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (tricanonical f) := by
  let := GenusNineDualizingModel.dualizing_isInvertible f
  exact CanonicalHilbertFunction.canonicalPower_isInvertible f 3

variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

theorem tricanonical_degree (hdim : topologicalKrullDim X ≤ 1) (hg : genus f=9) :
    invertibleCurveDegree k f hdim (tricanonical f)=48 := by
  let := GenusNineDualizingModel.dualizing_isInvertible f
  have h := invertibleCurveDegree_tensorPower_eq_mul k f hdim (dualizingSheafOverField f)
    (@invertibleCurveDegree_tensorSheaf_eq_add k _ X f _ hdim) (3 : ℤ)
  change invertibleCurveDegree k f hdim (tricanonical f)=
    3*invertibleCurveDegree k f hdim (dualizingSheafOverField f) at h
  calc
    _ = 3*invertibleCurveDegree k f hdim (dualizingSheafOverField f) := h
    _ = 48 := by
      rw [CanonicalLineCohomology.canonical_degree f hdim,hg]
      norm_num

theorem tricanonical_h0 (hdim : topologicalKrullDim X ≤ 1) (hg : genus f=9) :
    Module.finrank k (cohomologyOverField k f (tricanonical f) 0)=40 := by
  let := GenusNineDualizingModel.dualizing_isInvertible f
  have h := CanonicalHilbertFunction.canonical_power_h0 f hdim hg 3 (by decide)
  norm_num at h
  exact_mod_cast h

theorem tricanonical_h1_isZero (hdim : topologicalKrullDim X ≤ 1) (hg : genus f=9) :
    IsZero (cohomologyOverField k f (tricanonical f) 1) := by
  let := GenusNineDualizingModel.dualizing_isInvertible f
  apply CanonicalHilbertFunction.h1_isZero_of_canonical_degree_lt f hdim (tricanonical f)
  rw [tricanonical_degree f hdim hg,CanonicalLineCohomology.canonical_degree f hdim,hg]
  norm_num

end M9Native.GenusNineTricanonicalCohomology
end

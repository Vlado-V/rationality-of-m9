module

public import M9StacksIntegration.CanonicalRestrictionDuality
public import StacksFrontier.AlgebraicGeometry.InvertibleModuleEndomorphismOverField
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch

/-!
# Cohomology and degree of the actual canonical line

Invertibility of the actual dualizing sheaf identifies its endomorphism
space with the constants. Actual native Serre duality gives h¹(ω)=1;
h⁰(ω)=g and actual line Riemann--Roch give deg(ω)=2g−2. No determinant
bundle, canonical-degree premise, or chosen H¹-dimension is supplied.
The separate smooth-curve theorem supplies invertibility itself.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

universe u

namespace M9Native.CanonicalLineCohomology

open CategoryTheory AlgebraicGeometry
open Stacks.Duality (dualizingSheafOverField)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable (hdim : topologicalKrullDim X ≤ 1)
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
  (dualizingSheafOverField f)]

include hdim

/-- Actual scalar endomorphisms and native Serre duality compute
the first cohomology of the actual canonical line. -/
theorem canonical_h1_eq_one :
    Module.finrank k (cohomologyOverField k f (dualizingSheafOverField f) 1) = 1 := by
  let := modulesLinearOverField k f
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualizingSheafOverField f) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X _
  let : (dualizingSheafOverField f).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
      k f (dualizingSheafOverField f) 1
  let : Module.Finite k (cohomologyOverField k f (dualizingSheafOverField f) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f _ 1
  have h : Module.finrank k ((dualizingSheafOverField f) ⟶ (dualizingSheafOverField f)) =
      Module.finrank k (cohomologyOverField k f (dualizingSheafOverField f) 1) :=
    (Stacks.Duality.homDualizingSheafLinearEquiv f hdim
      (dualizingSheafOverField f) (isQuasicoherent_of_isCoherent _)).finrank_eq.trans
        Subspace.dual_finrank_eq
  exact h.symm.trans (finrank_end_eq_one_of_isInvertible k f _)

/-- The degree of the actual canonical line, derived from its actual
cohomology and native line Riemann--Roch. -/
theorem canonical_degree :
    invertibleCurveDegree k f hdim (dualizingSheafOverField f) = 2 * (genus f : ℤ) - 2 := by
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus
    k f hdim (dualizingSheafOverField f)
  rw [Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim,
    canonical_h1_eq_one f hdim] at h
  push_cast at h
  linarith

end M9Native.CanonicalLineCohomology

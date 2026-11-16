module

public import M9StacksIntegration.CanonicalLineCohomology
public import M9StacksIntegration.MukaiCanonicalTwistBounds
public import M9StacksIntegration.MukaiNoDegreeSevenNet
public import M9StacksIntegration.MukaiCompleteEvaluation
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The actual residual complete degree-eight net

Starting with one native degree-eight net on the original nonpentagonal
genus-nine curve, the low-degree-net obstruction proves that it is complete.
Native line Riemann--Roch computes its first cohomology. Native Serre
duality then computes the sections of the literal residual sheaf
`dualizingSheafOverField f ⊗ dualSheaf A.L`.

The actual residual tensor isomorphism gives its degree, and its full
section space defines the residual native linear series. The original
complete-net evaluation is epimorphic for every chosen complete basis.
This leaf uses true invertibility of the actual native dualizing sheaf;
it assumes no canonical degree, second net, or rank-three bundle.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Opposite
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiResidualNet

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The underlying residual is the actual native tensor with the dual. -/
abbrev residualNetLine (A : LinearSeries k f hdim 8 2) : X.Modules :=
  residualLine (Stacks.Duality.dualizingSheafOverField f) A.L

/-- The count for the original net is derived from nonpentagonality. -/
theorem original_h0_eq_three (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    Module.finrank k (cohomologyOverField k f A.L 0) = 3 :=
  (MukaiNoDegreeSevenNet.degree_eight_net_h0_eq_three_and_complete
    f hdim hg hnp A).1

/-- Actual line Riemann--Roch gives the three first-cohomology classes
of the original degree-eight line in genus nine. -/
theorem original_h1_eq_three (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    Module.finrank k (cohomologyOverField k f A.L 1) = 3 := by
  let := A.isInvertible
  let := isIso_globalSections_of_isAlgClosed k f
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim A.L
  rw [A.degree_eq, hg, original_h0_eq_three f hdim hg hnp A] at h
  omega

omit [IsAlgClosed k] [IsCurve k f] in
/-- Native tensor--Hom and base-field-linear Serre duality identify the
residual section count with the original first cohomology. This identity
does not require invertibility of the canonical sheaf. -/
theorem residualNetLine_h0_eq_h1 (A : LinearSeries k f hdim 8 2) :
    Module.finrank k (cohomologyOverField k f (residualNetLine f hdim A) 0) =
      Module.finrank k (cohomologyOverField k f A.L 1) := by
  let := A.isInvertible
  let := modulesLinearOverField k f
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X A.L
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : A.L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X A.L
  let := finiteDimensional_cohomologyOverField_of_isProper k f A.L 1
  let e₁ := MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f A.L
    (Stacks.Duality.dualizingSheafOverField f)
  let e₂ := cohomologyOverFieldIso k f
    (Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank A.L
      (Stacks.Duality.dualizingSheafOverField f) 1).symm 0
  have heq : Module.finrank k (A.L ⟶ Stacks.Duality.dualizingSheafOverField f) =
      Module.finrank k (cohomologyOverField k f (residualNetLine f hdim A) 0) :=
    (e₁.trans e₂.toLinearEquiv).finrank_eq
  rw [← heq, (Stacks.Duality.homDualizingSheafLinearEquiv f hdim A.L
    (isQuasicoherent_of_isCoherent _)).finrank_eq, Subspace.dual_finrank_eq]

/-- The three sections of the residual are derived from actual
Riemann--Roch and Serre duality, without a second-net existence premise. -/
theorem residualNetLine_h0_eq_three (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    Module.finrank k (cohomologyOverField k f (residualNetLine f hdim A) 0) = 3 :=
  (residualNetLine_h0_eq_h1 f hdim A).trans
    (original_h1_eq_three f hdim hg hnp A)

variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
  (Stacks.Duality.dualizingSheafOverField f)]

omit [IsAlgClosed k] [IsCurve k f] [Smooth f] in
/-- True invertibility of the native canonical line gives invertibility
of the literal residual, without using a second net. -/
theorem residualNetLine_isInvertible (A : LinearSeries k f hdim 8 2) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (residualNetLine f hdim A) := by
  let := A.isInvertible
  exact residualLine_isInvertible _ A.L

/-- Canonical degree is calculated from actual canonical cohomology;
tensor cancellation then gives degree eight for the residual. -/
theorem residualNetLine_degree (hg : genus f = 9)
    (A : LinearSeries k f hdim 8 2) :
    letI := residualNetLine_isInvertible f hdim A
    invertibleCurveDegree k f hdim (residualNetLine f hdim A) = 8 := by
  let := A.isInvertible
  let := isIso_globalSections_of_isAlgClosed k f
  let := residualNetLine_isInvertible f hdim A
  have hC := CanonicalLineCohomology.canonical_degree f hdim
  have h := MukaiCanonicalTwistBounds.residual_degree f hdim hC hg A.L
  change invertibleCurveDegree k f hdim (residualNetLine f hdim A) =
    16 - invertibleCurveDegree k f hdim A.L at h
  rw [A.degree_eq] at h
  norm_num at h
  exact h

/-- The residual native degree-eight net uses its actual full section
space. Neither a second-net existence assumption nor chosen section
subspace is supplied. -/
def residualNet (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) : LinearSeries k f hdim 8 2 where
  L := residualNetLine f hdim A
  isInvertible := residualNetLine_isInvertible f hdim A
  degree_eq := residualNetLine_degree f hdim hg A
  V := ⊤
  finrank_eq := by
    simpa only [finrank_top, Nat.reduceAdd] using
      residualNetLine_h0_eq_three f hdim hg hnp A

@[simp]
theorem residualNet_L (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    (residualNet f hdim hg hnp A).L =
      residualLine (Stacks.Duality.dualizingSheafOverField f) A.L := rfl

@[simp]
theorem residualNet_V (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    (residualNet f hdim hg hnp A).V = ⊤ := rfl

/-- The actual residual tensor isomorphism is the canonical cancellation
isomorphism, with the constructed native residual as its target factor. -/
def residualNetTensorIso (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    tensor A.L (residualNet f hdim hg hnp A).L ≅
      Stacks.Duality.dualizingSheafOverField f := by
  let := A.isInvertible
  exact residualTensorIso (Stacks.Duality.dualizingSheafOverField f) A.L

/-- Construct a complete cohomology basis for the literal residual. -/
def residualNetBasis (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    Module.Basis (ULift.{u} (Fin 3)) k
      (cohomologyOverField k f (residualNet f hdim hg hnp A).L 0) := by
  let B := residualNet f hdim hg hnp A
  let := B.isInvertible
  let := CurveDivisorSections.invertible_cohomology_zero_finite f B.L
  let : Module.Free k (cohomologyOverField k f B.L 0) :=
    Module.Free.of_divisionRing k (cohomologyOverField k f B.L 0)
  exact (Module.finBasisOfFinrankEq k (cohomologyOverField k f B.L 0)
    (residualNetLine_h0_eq_three f hdim hg hnp A)).reindex Equiv.ulift.symm

/-- The section tuple is precisely the public complete-net construction
from the actual residual cohomology basis. -/
def residualNetSections (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    ULift.{u} (Fin 3) → (residualNet f hdim hg hnp A).L.sections :=
  completeNetSections f (residualNet f hdim hg hnp A).L
    (residualNetBasis f hdim hg hnp A)

@[simp]
theorem residualNetSections_eval_top (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) (i : ULift.{u} (Fin 3)) :
    (residualNetSections f hdim hg hnp A i).eval (op ⊤) =
      (cohomologyOverFieldZeroLinearIso k f (residualNet f hdim hg hnp A).L).hom
        (residualNetBasis f hdim hg hnp A i) :=
  completeNetSections_eval_top f _ _ i

/-- Every actual complete residual basis generates the original sheaf,
by the proved absence of lower-degree nets on the original curve. -/
theorem residualNet_evaluation_epi (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2)
    (b : Module.Basis (ULift.{u} (Fin 3)) k
      (cohomologyOverField k f (residualNet f hdim hg hnp A).L 0)) :
    Epi (netEvaluation (residualNet f hdim hg hnp A).L
      (completeNetSections f (residualNet f hdim hg hnp A).L b)) :=
  MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f hdim
    (MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f hdim hg hnp)
    (residualNet f hdim hg hnp A) b

/-- In particular, the actually constructed public residual section
tuple has epimorphic native evaluation. -/
theorem residualNetSections_evaluation_epi (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (A : LinearSeries k f hdim 8 2) :
    Epi (netEvaluation (residualNet f hdim hg hnp A).L
      (residualNetSections f hdim hg hnp A)) :=
  residualNet_evaluation_epi f hdim hg hnp A (residualNetBasis f hdim hg hnp A)

end M9Native.MukaiResidualNet

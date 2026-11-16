module

public import M9StacksIntegration.MukaiTensorDiagonal
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# Actual geometric hypotheses for the native Ext pairing

The tensor quotient is an actual finite locally free module by the
explicit unit isomorphism. Its quasi-coherence, coherence and finite
cohomology are derived. A smooth integral curve is Cohen--Macaulay and
equidimensional by the native geometric theorems. None of these standard
pairing hypotheses needs to be supplied as extra geometry data.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.MukaiCurvePairingGeometry

open M9Native.MukaiCupAlternating M9Native.MukaiTensorDiagonal

variable {X : Scheme.{u}}

/-- The actual quotient of the tensorized normalized sequence. -/
abbrev tensorQuotient (C : X.Modules) : X.Modules :=
  (tensorRight C).obj (_root_.SheafOfModules.unit X.ringCatSheaf)

/-- The actual unit isomorphism retains the actual quotient rank. -/
theorem tensorQuotient_rank (C : X.Modules) (r : ℕ)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensorQuotient C) r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (unitLeftIso C).symm hC

/-- Genuine finite local freeness supplies native quasi-coherence. -/
theorem quasicoherent_of_rank (C : X.Modules) (r : ℕ)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C r) : C.IsQuasicoherent := by
  let := hC
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree C r
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree C

/-- The actual tensor quotient is quasi-coherent. -/
theorem tensorQuotient_quasicoherent (C : X.Modules) (r : ℕ)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C r) :
    (tensorQuotient C).IsQuasicoherent :=
  quasicoherent_of_rank (tensorQuotient C) r (tensorQuotient_rank C r hC)

/-- Coherence of the quotient is proved on the original curve. -/
theorem tensorQuotient_coherent (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] (C : X.Modules) (r : ℕ)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C r) :
    (tensorQuotient C).IsCoherent := by
  let := tensorQuotient_rank C r hC
  exact SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve
    k f (tensorQuotient C) r

/-- Properness derives finite-dimensional cohomology of the actual
quotient, with the original native base-field action. -/
theorem tensorQuotient_cohomology_finite (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (C : X.Modules) (r : ℕ)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C r) (n : ℕ) :
    Module.Finite k (cohomologyOverField k f (tensorQuotient C) n) := by
  let := tensorQuotient_coherent k f C r hC
  exact finiteDimensional_cohomologyOverField_of_isProper k f (tensorQuotient C) n

/-- An actual integral curve is equidimensional; no equidimensionality
data is added to the original curve. -/
theorem curve_equidimensional (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] : TopologicalSpace.Equidimensional X :=
  TopologicalSpace.Equidimensional.of_preirreducibleSpace X

/-- Native smooth-to-syntomic and syntomic-to-Cohen--Macaulay prove the
geometric duality hypothesis for the actual smooth curve. -/
theorem smooth_curve_cohenMacaulay (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] : IsCohenMacaulay X :=
  isCohenMacaulay_of_syntomic_over_field f (syntomic_of_smooth f)

end M9Native.MukaiCurvePairingGeometry

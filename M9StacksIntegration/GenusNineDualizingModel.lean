module

public import M9StacksIntegration.DualizingDivisorRestriction
public import M9StacksIntegration.CurveDegreeTwoRestriction
public import M9StacksIntegration.CompleteProjectiveLinearSystem
public import M9StacksIntegration.CanonicalLineCohomology
public import M9StacksIntegration.CanonicalHilbertFunction
public import M9StacksIntegration.SmoothConnectedCurve
public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor
public import M9StacksIntegration.Private.CurveCanonicalInvertibility
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# The actual genus-nine dualizing model

Smoothness makes the actual curve regular and hence Gorenstein, so its
actual dualizing sheaf is invertible. Actual natural Serre duality and
the no-pencil argument separate every length-two closed subscheme.
Its nine sections therefore give a genuine closed immersion in P⁸,
with the original base map and the original pullback of O(1).

This is an intrinsic curve theorem. It neither defines a replacement
moduli space nor assumes a Mukai/coarse-space classification. The audit
records source-bound kernel status; the native normalized dualizing-complex
and model providers are a separate dependency gate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace M9Native.GenusNineDualizingModel

open CategoryTheory AlgebraicGeometry
open Stacks.Duality (dualizingSheafOverField)
open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The original dualizing module is invertible, by the native
Gorenstein theorem applied to the actual smooth curve. -/
theorem dualizing_isInvertible (f : X ⟶ Spec (.of k))
    [IsProper f] [IsCurve k f] [Smooth f] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (dualizingSheafOverField f) := by
  exact CurveCanonicalInvertibility.dualizing_isInvertible f

/-- Actual canonical numerical data, using the native derived
cohomology and the native degree of the original dualizing sheaf. -/
theorem canonical_numerical_data [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    [IsProper f] [IsCurve k f] [Smooth f] (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) :
    ∃ hω : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
        (dualizingSheafOverField f),
      letI := hω;
      invertibleCurveDegree k f hdim (dualizingSheafOverField f) = 16 ∧
        Module.finrank k (cohomologyOverField k f (dualizingSheafOverField f) 0) = 9 := by
  let : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  let hω := dualizing_isInvertible f
  let := hω
  refine ⟨hω, ?_, (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField
    f hdim).trans hg⟩
  calc
    _ = 2 * (genus f : ℤ) - 2 :=
      CanonicalLineCohomology.canonical_degree f hdim
    _ = 16 := by rw [hg]; norm_num

/-- The actual complete canonical series; no projective or moduli
identification is built into this native linear-series construction. -/
def canonicalSeries [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    [IsProper f] [IsCurve k f] [Smooth f] (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) : LinearSeries k f hdim 16 8 := by
  let hω := dualizing_isInvertible f
  let := hω
  exact
    { L := dualizingSheafOverField f
      isInvertible := hω
      degree_eq := by
        obtain ⟨_, hdeg, _⟩ := canonical_numerical_data f hdim hg
        exact hdeg
      V := ⊤
      finrank_eq := by
        obtain ⟨_, _, h0⟩ := canonical_numerical_data f hdim hg
        simpa only [finrank_top] using h0 }

/-- Nonpentagonality implies every actual canonical length-two
restriction is onto; both the Cartier and no-degree-two-pencil inputs
are derived on the original curve. -/
theorem canonical_surjectsOnDegreeTwo [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    [IsProper f] [IsCurve k f] [Smooth f] (hdim : topologicalKrullDim X ≤ 1)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) :
    SurjectsOnDegreeTwo f (dualizingSheafOverField f) := by
  let : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  let := dualizing_isInvertible f
  have hno2 := M9StacksIntegration.LinearSeriesAddEffectiveDivisor.no_degree_two_pencil_of_no_degree_five
    f hdim hnp
  exact CurveDegreeTwoRestriction.surjectsOnDegreeTwo_of_forall_restriction_surjective
    f (dualizingSheafOverField f)
    (M9StacksIntegration.DualizingDivisorRestriction.restriction_surjective_of_no_degree_two_pencil
      f hdim hno2)

/-- The actual genus-nine nonpentagonal curve has a genuine canonical
closed immersion in the exact native P⁸, with its actual O(1) pullback. -/
theorem exists_canonical_closedImmersion [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    [IsProper f] [IsCurve k f] [Smooth f] (hdim : topologicalKrullDim X ≤ 1)
    (hg : genus f = 9) (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) :
    ∃ φ : X ⟶ projectiveSpaceOver 8 (Spec (.of k)),
      IsClosedImmersion φ ∧
      φ ≫ Stacks.Tag01VT.projectiveSpaceHom 8 (Spec (.of k)) = f ∧
      Nonempty ((Scheme.Modules.pullback φ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 8 (Spec (.of k))) ≅
          dualizingSheafOverField f) := by
  let := dualizing_isInvertible f
  exact CompleteProjectiveLinearSystem.exists_closedImmersion_of_h0_eq_and_degree_two_separation
    f (dualizingSheafOverField f) 8
    ((Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim).trans hg)
    (canonical_surjectsOnDegreeTwo f hdim hnp)

/-- The same original curve embeds in the literal native polynomial
Proj model of P⁸, with its original structure morphism retained. -/
theorem exists_canonical_polynomialProjClosedImmersion [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1) (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) :
    ∃ φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 9) k),
      IsClosedImmersion φ ∧ φ ≫ projToSpecCoeff k 8 = f := by
  let := dualizing_isInvertible f
  exact CompleteProjectiveLinearSystem.exists_polynomialProjClosedImmersion_of_h0_eq_and_degree_two_separation
    f (dualizingSheafOverField f) 8
    ((Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim).trans hg)
    (canonical_surjectsOnDegreeTwo f hdim hnp)

/-- The actual powers of the canonical line have the canonical
genus-nine Hilbert value, with invertibility derived from smoothness. -/
theorem canonical_power_h0 [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1) (hg : genus f = 9) (t : ℕ) (ht : 2 ≤ t) :
    letI := dualizing_isInvertible f;
    (Module.finrank k (cohomologyOverField k f
      (CanonicalHilbertFunction.canonicalPower f t) 0) : ℤ) = 16 * (t : ℤ) - 8 := by
  let := dualizing_isInvertible f
  let : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  exact CanonicalHilbertFunction.canonical_power_h0 f hdim hg t ht

/-- The canonical embedding for the original geometric curve input:
proper, smooth, geometrically connected and dimension one. Integrality,
native curve structure and all canonical properties are derived. -/
theorem exists_canonical_closedImmersion_of_geometric_conditions [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : topologicalKrullDim X = 1) (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim.le 5 1)) :
    ∃ φ : X ⟶ projectiveSpaceOver 8 (Spec (.of k)),
      IsClosedImmersion φ ∧
      φ ≫ Stacks.Tag01VT.projectiveSpaceHom 8 (Spec (.of k)) = f ∧
      Nonempty ((Scheme.Modules.pullback φ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 8 (Spec (.of k))) ≅
          dualizingSheafOverField f) := by
  let : IsCurve k f := SmoothConnectedCurve.isCurve_of_smooth_geometricallyConnected f hdim
  exact exists_canonical_closedImmersion f hdim.le hg hnp

end M9Native.GenusNineDualizingModel

module

public import M9StacksIntegration.MinimalDegreeSeriesGeneration
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.PinnedTwist
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The literal moving part of a native pencil

The subsheaf spanned by the original two sections is finite, torsion free
of rank one on the original regular curve, hence invertible by the native
span theorem. Its original two lifted sections generate it. They remain
independent on actual cohomology by naturality of the original comparison.
Their span constructs a generated native pencil of nonnegative degree at
most the original degree. No basepoint-free or minimal-degree premise is
supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.LinearSeriesMorphism Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf

universe u

namespace M9Native.PencilBasepointRemoval

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}

/-- The original invertible line is genuinely quasi-coherent. -/
theorem original_quasicoherent (A : LinearSeries k f hdim d 1) : A.L.IsQuasicoherent := by
  let := A.isInvertible
  exact Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule A.L

/-- The actual evaluation span, as a native subsheaf of the original line. -/
def movingLine (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    X.Modules := by
  let := original_quasicoherent f hdim A
  exact spanRestrictModule A.L (Set.range (seriesSections A b))

/-- The literal inclusion of that evaluation span. -/
def movingInclusion (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    movingLine f hdim A b ⟶ A.L := by
  let := original_quasicoherent f hdim A
  exact spanRestrictSubsheafι A.L (Set.range (seriesSections A b))

/-- The original two sections, now as sections of the native span. -/
def movingSections (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    Fin 2 → Γ(movingLine f hdim A b, ⊤) := by
  let := original_quasicoherent f hdim A
  exact spanRangeSection A.L (seriesSections A b)

/-- The inclusion is actually injective over every open. -/
theorem movingInclusion_app_injective (A : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k A.V) (U : X.Opens) :
    Function.Injective ((movingInclusion f hdim A b).app U) := by
  let := original_quasicoherent f hdim A
  exact injective_app_spanRestrictSubsheafι A.L (Set.range (seriesSections A b)) U

@[simp]
theorem movingInclusion_sections (A : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k A.V) (i : Fin 2) :
    (movingInclusion f hdim A b).app ⊤ (movingSections f hdim A b i) =
      seriesSections A b i := by
  let := original_quasicoherent f hdim A
  exact app_spanRestrictSubsheafι_spanRangeSection A.L (seriesSections A b) i

/-- The original lifted sections generate the actual evaluation span. -/
theorem movingSections_generate (A : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k A.V) :
    GeneratesStalks (movingSections f hdim A b) := by
  let := original_quasicoherent f hdim A
  exact generatesStalks_spanRangeSection A.L (seriesSections A b)

/-- The literal evaluation span is invertible on the original smooth curve. -/
theorem movingLine_isInvertible [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (movingLine f hdim A b) := by
  let := A.isInvertible
  let := original_quasicoherent f hdim A
  let : IsLocallyNoetherian X :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k f
  have hgerm := Stacks.AlgebraicGeometry.ReflexiveModules.Γgerm_genericPoint_ne_zero_of_ne_zero A.L
    (seriesSections_ne_zero A b 0)
  exact Stacks.AlgebraicGeometry.ReflexiveModules.isInvertibleModule_spanRestrictModule A.L
    (isRegular_of_smooth_over_field f) hdim (seriesSections A b) (Set.finite_range _) hgerm

/-- The native section classes of the literal lifted sections. -/
def movingClasses (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    Fin 2 → cohomologyOverField k f (movingLine f hdim A b) 0 :=
  fun i => (cohomologyOverFieldZeroEquivSections k f (movingLine f hdim A b)).symm
    (movingSections f hdim A b i)

/-- Naturality, rather than an assumed section-independence statement,
proves independence of the actual moving classes. -/
theorem movingClasses_linearIndependent (A : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k A.V) : LinearIndependent k (movingClasses f hdim A b) := by
  let q := (cohomologyOverFieldMap k f (movingInclusion f hdim A b) 0).hom
  have hqt (i : Fin 2) : q (movingClasses f hdim A b i) =
      (b i : cohomologyOverField k f A.L 0) := by
    apply (cohomologyOverFieldZeroEquivSections k f A.L).injective
    rw [cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap]
    change (movingInclusion f hdim A b).app ⊤
      ((cohomologyOverFieldZeroEquivSections k f (movingLine f hdim A b))
        ((cohomologyOverFieldZeroEquivSections k f (movingLine f hdim A b)).symm
          (movingSections f hdim A b i))) = _
    rw [Equiv.apply_symm_apply]
    exact movingInclusion_sections f hdim A b i
  refine LinearIndependent.of_comp q ?_
  have hfun : q ∘ movingClasses f hdim A b =
      fun i => (b i : cohomologyOverField k f A.L 0) := funext hqt
  rw [hfun]
  exact b.linearIndependent.map' A.V.subtype (by simp)

/-- The moving inclusion is nonzero because it carries the original
nonzero first section. -/
theorem movingInclusion_ne_zero (A : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k A.V) : movingInclusion f hdim A b ≠ 0 :=
  MinimalDegreeSeriesGeneration.lift_map_ne_zero f hdim A b
    (movingInclusion f hdim A b) (movingSections f hdim A b)
    (movingInclusion_sections f hdim A b)

/-- The actual moving line has degree between zero and the original degree. -/
theorem movingLine_degree_bounds [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    letI := movingLine_isInvertible f hdim A b
    0 ≤ invertibleCurveDegree k f hdim (movingLine f hdim A b) ∧
      invertibleCurveDegree k f hdim (movingLine f hdim A b) ≤ (d : ℤ) := by
  let := A.isInvertible
  let := movingLine_isInvertible f hdim A b
  have hs : movingSections f hdim A b 0 ≠ 0 := by
    intro hzero
    apply seriesSections_ne_zero A b 0
    rw [← movingInclusion_sections f hdim A b 0, hzero, map_zero]
  let s : (movingLine f hdim A b).sections :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X (movingLine f hdim A b)).symm
      (movingSections f hdim A b 0)
  have heval : s.eval (op ⊤) = movingSections f hdim A b 0 :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X (movingLine f hdim A b)).apply_symm_apply _
  refine ⟨invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim _ s (by rwa [heval]), ?_⟩
  have h := invertibleCurveDegree_le_of_hom_ne_zero k f hdim
    (movingLine f hdim A b) A.L (movingInclusion f hdim A b)
    (movingInclusion_ne_zero f hdim A b)
  exact h.trans A.degree_eq.le

/-- The degree of the actual moving line, as a natural number. -/
def movingDegree [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) : ℕ := by
  let := movingLine_isInvertible f hdim A b
  exact (invertibleCurveDegree k f hdim (movingLine f hdim A b)).toNat

theorem movingDegree_cast [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    letI := movingLine_isInvertible f hdim A b
    (movingDegree f hdim A b : ℤ) = invertibleCurveDegree k f hdim (movingLine f hdim A b) :=
  Int.toNat_of_nonneg (movingLine_degree_bounds f hdim A b).1

theorem movingDegree_le [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    movingDegree f hdim A b ≤ d := by
  let := movingLine_isInvertible f hdim A b
  have hb := (movingLine_degree_bounds f hdim A b).2
  rw [← movingDegree_cast f hdim A b] at hb
  exact_mod_cast hb

/-- The actual generated pencil after removing the base locus of the
original pair, keeping precisely its two lifted section classes. -/
def movingPencil [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    LinearSeries k f hdim (movingDegree f hdim A b) 1 where
  L := movingLine f hdim A b
  isInvertible := movingLine_isInvertible f hdim A b
  degree_eq := (movingDegree_cast f hdim A b).symm
  V := Submodule.span k (Set.range (movingClasses f hdim A b))
  finrank_eq := by
    simpa only [Fintype.card_fin, Nat.reduceAdd] using
      finrank_span_eq_card (movingClasses_linearIndependent f hdim A b)

/-- The moving pencil's native basis is the span basis of its original
lifted two classes, so it remembers the original pair. -/
def movingPencilBasis [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    Module.Basis (Fin 2) k (movingPencil f hdim A b).V :=
  Module.Basis.span (movingClasses_linearIndependent f hdim A b)

@[simp]
theorem movingPencilBasis_sections [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) (i : Fin 2) :
    seriesSections (movingPencil f hdim A b) (movingPencilBasis f hdim A b) i =
      movingSections f hdim A b i := by
  change (cohomologyOverFieldZeroEquivSections k f (movingLine f hdim A b))
    ((Module.Basis.span (movingClasses_linearIndependent f hdim A b)) i :
      cohomologyOverField k f (movingLine f hdim A b) 0) = _
  rw [Module.Basis.coe_span_apply]
  exact (cohomologyOverFieldZeroEquivSections k f (movingLine f hdim A b)).apply_symm_apply _

/-- Generation is derived for the original basis of the moving pencil. -/
theorem movingPencil_generates [IsCurve k f] [Smooth f]
    (A : LinearSeries k f hdim d 1) (b : Module.Basis (Fin 2) k A.V) :
    GeneratesStalks (seriesSections (movingPencil f hdim A b)
      (movingPencilBasis f hdim A b)) := by
  have heq : seriesSections (movingPencil f hdim A b) (movingPencilBasis f hdim A b) =
      movingSections f hdim A b := funext (movingPencilBasis_sections f hdim A b)
  rw [heq]
  exact movingSections_generate f hdim A b

end M9Native.PencilBasepointRemoval

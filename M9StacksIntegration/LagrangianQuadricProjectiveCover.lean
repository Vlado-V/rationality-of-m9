module

public import M9StacksIntegration.LagrangianTranslatedQuadricFamily
public import M9StacksIntegration.LagrangianQuadricPrimeCover
public import M9StacksIntegration.HomogeneousEquationPoints
public import M9StacksIntegration.LagrangianAdmissibleCoordinateIndices
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover

/-! The eight genuine admissible coordinate opens cover the entire
actual finite quadratic zero scheme. Prime membership is used only to
prove an open cover; no ideal or scheme is replaced by its radical. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianQuadricProjectiveCover

open LagrangianHomogeneousQuadrics LagrangianPrimitiveQuadrics
open LagrangianTranslatedQuadricFamily

open LagrangianAdmissibleCoordinateIndices

variable (K : Type u) [Field K]

/-- Every actual homogeneous prime containing the original quadrics
misses one of the eight actual admissible coordinates. -/
theorem exists_admissible_basicOpen (p : AlgebraicGeometry.Proj (polyGrading K 13))
    (hQ : ∀ i, LagrangianPrimitiveQuadrics.quadric K i ∈ p.asHomogeneousIdeal) :
    ∃ i : AdmissibleIndex, p ∈ Proj.basicOpen (polyGrading K 13) (X (admissibleIndex i)) := by
  let ρ : LagrangianHomogeneousQuadrics.Ring K →+* MvPolynomial (Fin 14) K :=
    (MvPolynomial.rename coordinateIndexEquiv).toRingHom
  let I := p.asHomogeneousIdeal.toIdeal.comap ρ
  letI : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  have hI : I.IsPrime := inferInstance
  have hQi (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
      LagrangianHomogeneousQuadrics.quadric K i ∈ I := hQ i
  have hX : ¬ ∀ j : CoordinateIndex.{u}, X j ∈ I := by
    intro hall
    apply p.not_irrelevant_le
    apply (irrelevant_le_span_X K 13).trans
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨j, rfl⟩ := coordinateIndexEquiv.surjective j
    have hj : MvPolynomial.rename coordinateIndexEquiv
        (X j : LagrangianHomogeneousQuadrics.Ring K) ∈ p.asHomogeneousIdeal.toIdeal := hall j
    rw [MvPolynomial.rename_X] at hj
    exact hj
  obtain ⟨i, hi⟩ := LagrangianQuadricPrimeCover.exists_admissible_not_mem K I hI hQi hX
  refine ⟨i, ?_⟩
  change MvPolynomial.rename coordinateIndexEquiv (admissibleCoordinate K i) ∉
    p.asHomogeneousIdeal.toIdeal at hi
  change X (admissibleIndex i) ∉ p.asHomogeneousIdeal.toIdeal
  exact (rename_admissibleCoordinate K i) ▸ hi

variable [CharZero K]

def zeroScheme : Scheme.{u} := (familyIdeal K).subscheme
def zeroInclusion : zeroScheme K ⟶ AlgebraicGeometry.Proj (polyGrading K 13) :=
  (familyIdeal K).subschemeι

def chart (i : AdmissibleIndex) : (zeroScheme K).Opens :=
  zeroInclusion K ⁻¹ᵁ Proj.basicOpen (polyGrading K 13) (X (admissibleIndex i))

theorem originalQuadric_mem (x : zeroScheme K) (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    LagrangianPrimitiveQuadrics.quadric K i ∈ (zeroInclusion K x).asHomogeneousIdeal :=
  HomogeneousEquationPoints.form_mem_homogeneousPrime K 13 2 (familyForm K) x (Sum.inl (), i)

/-- This is an open cover of the full genuine closed scheme, whose
local ring structures have not been altered. -/
theorem charts_cover (x : zeroScheme K) : ∃ i : AdmissibleIndex, x ∈ chart K i :=
  exists_admissible_basicOpen K (zeroInclusion K x) (originalQuadric_mem K x)

end M9Native.LagrangianQuadricProjectiveCover

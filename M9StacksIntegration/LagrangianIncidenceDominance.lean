module

public import M9StacksIntegration.LagrangianIncidenceFieldPoints
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Surjectivity of the original universal LG incidence projection.
The projective-intersection point construction hits every closed point
over an algebraically closed field. Its original proper projection has
closed image, and the native quotient parameter scheme is Jacobson.
Thus the projection is surjective, not merely dominant. Surjectivity
after arbitrary base change gives nonempty actual field-valued fibres. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open M9Native.LagrangianLinearSections M9Native.LagrangianIncidenceFieldPoints

universe u

namespace M9Native.LagrangianIncidenceDominance

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]

theorem familyProjection_surjective : Function.Surjective (familyProjection K) := by
  let : IsProper (parameterProjection K) := isProper_of_isProjectiveMorphism _
    (AlgebraicGeometry.Grassmannian.isProjectiveMorphism_schemeOver 9 14 (Spec (.of K)))
  let : JacobsonSpace (parameter K) :=
    LocallyOfFiniteType.jacobsonSpace (parameterProjection K)
  have hclosed : IsClosed (Set.range (familyProjection K)) :=
    (familyProjection K).isClosedMap.isClosed_range
  have hpoints : closedPoints (parameter K) ⊆ Set.range (familyProjection K) := by
    intro y hy
    let p := pointOfClosedPoint (parameterProjection K) y hy
    obtain ⟨z, hz⟩ := exists_familyPoint_of_parameterPoint K p
      (pointOfClosedPoint_comp _ _ _)
    refine ⟨z (IsLocalRing.closedPoint K), ?_⟩
    have h := congrArg (fun q : Spec (.of K) ⟶ parameter K => q (IsLocalRing.closedPoint K)) hz
    simpa only [Scheme.Hom.comp_apply, p, pointOfClosedPoint_apply] using h
  have hd := closure_minimal hpoints hclosed
  rw [closure_closedPoints] at hd
  intro y
  exact hd (Set.mem_univ y)

instance familyProjection_isSurjective : Surjective (familyProjection K) :=
  ⟨familyProjection_surjective K⟩

instance familyProjection_isDominant : IsDominant (familyProjection K) := inferInstance

/-- The actual scheme-theoretic fibre over every field-valued parameter
point is nonempty; the point need not be closed or rational over K. -/
theorem fieldPoint_fibre_nonempty {L : Type u} [Field L]
    (p : Spec (.of L) ⟶ parameter K) :
    Nonempty ↥(pullback p (familyProjection K) : Scheme.{u}) := by
  obtain ⟨x, -⟩ := (pullback.fst p (familyProjection K)).surjective
    (IsLocalRing.closedPoint L)
  exact ⟨x⟩

/-- Surjectivity is retained over every actual base change. -/
theorem familyProjection_baseChange_surjective {T : Scheme.{u}} (p : T ⟶ parameter K) :
    Function.Surjective (pullback.fst p (familyProjection K)) :=
  (pullback.fst p (familyProjection K)).surjective

end M9Native.LagrangianIncidenceDominance

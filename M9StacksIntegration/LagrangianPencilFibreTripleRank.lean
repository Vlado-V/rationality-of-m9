module

public import M9StacksIntegration.RationalPointDivisor
public import M9StacksIntegration.LagrangianPencilFourPointFibre

/-!
# Canonical rank of every selected actual pencil-fibre triple

All four distinct points come from the original degree-four pencil.
Each triple constructs its literal reduced Cartier divisor of length
three, so the genuine no-degree-three theorem and Riemann--Roch give
canonical rank three. No triple independence or rank premise is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianPencilFibreTripleRank

open PencilFourPointFibre LagrangianTransverseRestriction

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} [IsCurve K f]

/-- The selected rational curve maps identify actual closed points. -/
def closedPoint (D : FourPointFibre K f) (i : Fin 4) : closedPoints X :=
  pointEquivClosedPoint f ⟨curvePoint D i,curvePoint_overBase D i⟩

/-- Distinctness of the original points is a theorem of the full fibre. -/
theorem closedPoint_injective (D : FourPointFibre K f) :
    Function.Injective (closedPoint D) := by
  intro i j h
  apply curvePoint_injective D
  exact congrArg Subtype.val ((pointEquivClosedPoint f).injective h)

/-- Omitting each label selects all four triples of original points. -/
def triplePoints (D : FourPointFibre K f) (j : Fin 4) : Fin 3 → closedPoints X :=
  j.removeNth (closedPoint D)

theorem triplePoints_injective (D : FourPointFibre K f) (j : Fin 4) :
    Function.Injective (triplePoints D j) :=
  (closedPoint_injective D).comp Fin.succAbove_right_injective

variable [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- The original LG curve and its actual pencil produce the full fibre
and canonical rank three for EVERY triple of its four distinct points. -/
theorem exists_fourPointFibre_all_triple_rank
    (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (curve K M) ≤ 1)
    (A : LinearSeries K (curveProjection K M) hdim 4 1) :
    ∃ D : FourPointFibre K (curveProjection K M),
      ∀ j : Fin 4, Module.finrank K (LinearMap.range
        (CanonicalDivisorSpan.canonicalRestriction (curveProjection K M)
          (RationalPointDivisor.divisor (triplePoints D j)))) = 3 := by
  let : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  let := isIso_globalSections_of_isAlgClosed K (curveProjection K M)
  obtain ⟨D⟩ := LagrangianPencilFourPointFibre.nonempty_fourPointFibre K M hM hdim A
  exact ⟨D, fun j => RationalPointDivisor.canonical_rank_three (curveProjection K M)
    (triplePoints D j) (triplePoints_injective D j) hdim
    (LagrangianNoTrigonal.no_g1_three_at_dimension K M hM hdim)⟩

end M9Native.LagrangianPencilFibreTripleRank

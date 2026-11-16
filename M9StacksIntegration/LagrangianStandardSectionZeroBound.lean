module

public import M9StacksIntegration.LagrangianStandardSectionZeroModel
public import M9StacksIntegration.SplitQuadricFiniteLinearSection
public import M9StacksIntegration.LagrangianTransverseSixSections

/-!
# The actual full standard-section zero scheme has H0 at most two

The original curve zero scheme is identified with the genuine quadric
linear section. Actual finiteness is derived from the original good-open
curve and its proved nonzero original section. The finite-quadric theorem
then bounds native structural H0, retaining every nilpotent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.LagrangianStandardSectionZeroBound

open LagrangianStandardSectionZeroModel LagrangianMatrixChart

variable (K : Type u) [Field K] [CharZero K]

/-- The native structural scalar map sends the original first vector
to the actual first free-sheaf basis section. -/
theorem constantVector_first {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    LagrangianUniversalSections.constantVector K f (Pi.single (0 : Fin 6) 1) =
      freeBasisSection X 6 0 := by
  classical
  simp [LagrangianUniversalSections.constantVector, Pi.single_apply]

/-- Full scheme-theoretic finiteness, as distinct from a length bound,
is the only needed intermediate input to the genuine quadric theorem. -/
theorem h0_le_two_of_isFinite (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) [IsFinite (zeroCurveProjection K M hM)] :
    finrank K (structureSheafCohomology (zeroCurveProjection K M hM) 0) ≤ 2 := by
  let e := zeroIsoLinearSection K M hM
  let q := SplitQuadricLinearSection.sectionProjection K (equations K M)
  have he : e.hom ≫ q = zeroCurveProjection K M hM := zeroIsoLinearSection_over K M hM
  letI : IsFinite q := SplitQuadricQuotientCoordinates.finite_target_of_iso
    K e (zeroCurveProjection K M hM) q he
  have hcoh := (SplitQuadricQuotientCoordinates.structureCohomologyIso K e
    (zeroCurveProjection K M hM) q he 0).toLinearEquiv.finrank_eq
  exact hcoh.trans_le (SplitQuadricFiniteLinearSection.finite_section_h0_le_two K (equations K M))

variable [IsAlgClosed K]

/-- Every actual original good-open matrix fibre supplies the required
finiteness internally; no finiteness, support or reducedness premise remains. -/
theorem goodOpen_standard_zero_isFinite (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec)
    (hg : LagrangianMatrixPointRows.matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen K) :
    IsFinite (zeroCurveProjection K M hM) := by
  have hp : LagrangianMatrixPointRows.matrixPoint K M hM ≫
      LagrangianLinearSections.parameterProjection K = 𝟙 _ :=
    SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM
  have hv : (Pi.single (0 : Fin 6) (1 : K) : Fin 6 → K) ≠ 0 := by
    intro h
    have hc := congrFun h 0
    simpa using hc
  have h := LagrangianTransverseSixSections.goodOpen_zeroScheme_isFinite K
    (LagrangianMatrixPointRows.matrixPoint K M hM) hp hg (Pi.single 0 1) hv
  change IsFinite ((Stacks.Chow.zeroSchemeOfSection (curve K M hM)
    (LagrangianUniversalSections.bundle K (toLG K M hM))
    ((LagrangianUniversalSections.quotientMap K (toLG K M hM)).app ⊤
      (LagrangianUniversalSections.constantVector K (curveProjection K M hM)
        (Pi.single 0 1)))).subschemeι ≫ curveProjection K M hM) at h
  have hs : (LagrangianUniversalSections.quotientMap K (toLG K M hM)).app ⊤
      (LagrangianUniversalSections.constantVector K (curveProjection K M hM)
        (Pi.single 0 1)) = curveSection K M hM :=
    congrArg ((LagrangianUniversalSections.quotientMap K (toLG K M hM)).app ⊤)
      (constantVector_first K (curveProjection K M hM))
  exact (congrArg
    (fun s : Γ(LagrangianUniversalSections.bundle K (toLG K M hM), ⊤) =>
      IsFinite ((Stacks.Chow.zeroSchemeOfSection (curve K M hM)
        (LagrangianUniversalSections.bundle K (toLG K M hM)) s).subschemeι ≫
          curveProjection K M hM)) hs).mp h

/-- Mukai II4.4(1) for the literal original first quotient section on
every actual original good-open fibre, with full native scheme structure. -/
theorem goodOpen_standard_zero_h0_le_two (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec)
    (hg : LagrangianMatrixPointRows.matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
      LagrangianLinearSectionGenericSmooth.goodOpen K) :
    finrank K (structureSheafCohomology (zeroCurveProjection K M hM) 0) ≤ 2 := by
  letI := goodOpen_standard_zero_isFinite K M hM hg
  exact h0_le_two_of_isFinite K M hM

end M9Native.LagrangianStandardSectionZeroBound

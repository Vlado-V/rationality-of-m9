module

public import M9.RadicalMapTransport
public import M9.PrimitiveRadicalFiber
public import M9.PrimitiveOpenOrbitGeometry

/-! # Actual radical fibers over the checked dense principal orbit locus -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace M9.PrimitiveRadicalFiber

open Module ExteriorPrimitive PrimitiveStabilizer RadicalMap

variable (K : Type*) [Field K] [CharZero K]

local instance primitiveSliceAddCommGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

/-- The actual symplectic action transports exact fibers of the actual radical map. -/
def sp6FiberEquiv (h : Sp6 K) (L : Projectivization K (Primitive K)) :
    {U : RankEightNinePlanes K // radicalLineMap K U = L} ≃
      {U : RankEightNinePlanes K // radicalLineMap K U = projectiveAction K h L} := by
  have hact : projectiveAction K h L =
      Projectivization.map (primitiveLinear K h).toLinearMap (primitiveLinear K h).injective L := rfl
  rw [hact]
  exact RadicalMap.pointFiberIsometryEquiv (primitivePairing K) (primitivePairing_isAlt K)
    (primitiveLinear K h) (primitivePairing_invariant K h) L

/-- Every fiber over the proved dense principal orbit locus is an actual
nondegenerate four-plane Grassmannian fiber in the actual reduced space. -/
theorem complex_dense_open_fiber_comparison :
    ∃ f : PrimitiveOpenOrbit.ParameterRing ℂ,
      Dense (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (PrimitiveOpenOrbit.ParameterRing ℂ))) ∧
      PrimitiveOpenOrbit.evalBase ℂ f ≠ 0 ∧
      ∀ y : Fin 13 → ℂ, MvPolynomial.eval y f ≠ 0 →
        Nonempty
          ({U : RankEightNinePlanes ℂ // radicalLineMap ℂ U =
              PrimitiveOpenOrbitGeometry.chartProjective ℂ y} ≃
            RadicalFiber.NondegenerateSubspace
              (RadicalFiber.reducedForm (primitivePairing ℂ) (primitivePairing_isAlt ℂ)
                (rhoLine ℂ)) 4) := by
  obtain ⟨f,hDense,hBase,hOrbit⟩ :=
    PrimitiveOpenOrbitGeometry.complex_dense_principal_open_projective_orbit
  refine ⟨f,hDense,hBase,?_⟩
  intro y hy
  obtain ⟨h,hh⟩ := hOrbit y hy
  have e := sp6FiberEquiv ℂ h (rhoProjective ℂ)
  rw [hh] at e
  exact ⟨e.symm.trans (rhoFiberEquiv ℂ)⟩

end M9.PrimitiveRadicalFiber

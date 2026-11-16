module

public import M9StacksIntegration.MukaiEvaluationChoices

/-!
# The actual Mukai kernel line controls normalized basis choices

The true canonical exterior cohomology theorem supplies fourteen sections.
The actual semi-irreducibility exclusions then prove the kernel-line and
surjectivity assertions.  Naturality of the original exterior evaluation
derives the nonzero scalar between two normalized basis bivectors.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.MukaiKernelChoices

open MukaiLagrangianMap MukaiEvaluationChoices

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
  (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]

/-- The actual exterior kernel is a line and the actual lambda-two map is
surjective, using the genuine Semi3 consequences in addition to cohomology. -/
theorem canonical_lambdaTwo_kernel_line_and_surjective {E : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    finrank k (MukaiWedgeKernel.LambdaTwo k f E).ker = 1 ∧
      Function.Surjective (MukaiWedgeKernel.LambdaTwo k f E) := by
  let : FiniteDimensional k (H0 k f E) := b.finiteDimensional_of_finite
  have h6 : finrank k (H0 k f E) = 6 := by
    rw [finrank_eq_card_basis b, Fintype.card_fin]
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower E (2 : ℤ)) 3 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E 3 2
  let : (Scheme.Modules.exteriorPower E (2 : ℤ)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
      (Scheme.Modules.exteriorPower E (2 : ℤ)) 3
  let : FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower E (2 : ℤ)) 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f (Scheme.Modules.exteriorPower E (2 : ℤ)) 0
  exact MukaiSemiExclusions.lambdaTwo_kernel_line_and_surjective_of_semi k f E h6
    (MukaiCanonicalExteriorCohomology.curve_canonical_exterior_h0_fourteen k f E c hg h6) hsemi

omit [IsProper f] in
/-- Any normalized complete basis gives a genuine nondegenerate generator
of the original lambda-two kernel. -/
theorem basisSigma_kernel_nondegenerate {E : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) k (H0 k f E))
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (hb : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0) :
    (MukaiWedgeKernel.kernelMatrix k f E b (basisSigma k f E b)).det ≠ 0 := by
  let : FiniteDimensional k (H0 k f E) := b.finiteDimensional_of_finite
  exact MukaiSemiExclusions.lambdaTwo_kernel_nondegenerate_of_semi k f E b hsemi
    (basisSigma k f E b) (basisSigma_ne_zero k f b) hb

theorem kernel_eq_span_basisSigma {E : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (hb : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0) :
    (MukaiWedgeKernel.LambdaTwo k f E).ker = k ∙ basisSigma k f E b :=
  eq_span_singleton_of_mem_of_finrank_eq_one
    (canonical_lambdaTwo_kernel_line_and_surjective k f b c hg hsemi).1 hb
    (basisSigma_ne_zero k f b)

/-- The nonzero similitude multiplier is a consequence of actual bundle
naturality and the proved kernel line, not a pairing-scale hypothesis. -/
theorem exists_basisSigma_scale {E F : X.Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3]
    (e : E ≅ F) (bE : Basis (Fin 6) k (H0 k f E)) (bF : Basis (Fin 6) k (H0 k f F))
    (cF : Scheme.Modules.exteriorPower F (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f F 3)
    (hE : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E bE) = 0)
    (hF : ExteriorEvaluation.lambda k f F 2 (basisSigma k f F bF) = 0) :
    ∃ a : k, a ≠ 0 ∧
      exteriorPower.map 2 (h0Equiv k f e).toLinearMap (basisSigma k f E bE) =
        a • basisSigma k f F bF := by
  let y := exteriorPower.map 2 (h0Equiv k f e).toLinearMap (basisSigma k f E bE)
  have hy : y ∈ (MukaiWedgeKernel.LambdaTwo k f F).ker :=
    (lambda_kernel_transport k f e 2 (basisSigma k f E bE)).mpr hE
  have hy0 : y ≠ 0 := by
    intro hz
    apply basisSigma_ne_zero k f bE
    apply exteriorPower.map_injective_field (h0Equiv k f e).injective
    exact hz.trans (map_zero _).symm
  rw [kernel_eq_span_basisSigma k f bF cF hg hsemi hF] at hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  refine ⟨a, ?_, ha.symm⟩
  intro hz
  apply hy0
  simpa only [hz, zero_smul] using ha.symm

end M9Native.MukaiKernelChoices

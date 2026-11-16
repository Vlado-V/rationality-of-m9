module

public import StacksFrontier.RingTheory.FormallySmooth.FaithfullyFlatDescent
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Genuine extension of derivations across a formally smooth algebra

The actual Jacobi--Zariski sequence is split by formal smoothness.
The resulting retraction of the actual map on Kaehler differentials
extends every derivation with values in an actual module over the target.
No extension map or splitting is an input.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open scoped TensorProduct

namespace M9Native.FormallySmoothDerivationExtension
universe u v w z
variable (R : Type u) (B : Type v) (C : Type w)
  [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]

/-- Formal smoothness constructs an actual retraction of the actual
base-changed map on Kaehler differentials. -/
theorem exists_kaehler_retraction [Algebra.FormallySmooth B C] :
    ∃ r : Ω[C⁄R] →ₗ[C] C ⊗[B] Ω[B⁄R],
      r.comp (KaehlerDifferential.mapBaseChange R B C) = LinearMap.id := by
  obtain ⟨e, he, _⟩ :=
    Stacks.RingTheory.FormallySmoothDescent.exists_splitting_kaehlerDifferential R B C
  refine ⟨(LinearMap.fst C (C ⊗[B] Ω[B⁄R]) Ω[C⁄B]).comp e.toLinearMap, ?_⟩
  rw [he]
  ext ω
  simp

variable (M : Type z) [AddCommGroup M] [Module R M] [Module B M] [Module C M]
  [IsScalarTower R B M] [IsScalarTower R C M] [IsScalarTower B C M]

/-- Every actual relative derivation extends across a formally smooth
algebra map, with equality on the original algebra verified explicitly. -/
theorem exists_extension [Algebra.FormallySmooth B C] (D : Derivation R B M) :
    ∃ E : Derivation R C M, ∀ b : B, E (algebraMap B C b) = D b := by
  obtain ⟨r, hr⟩ := exists_kaehler_retraction R B C
  let L : Ω[C⁄R] →ₗ[C] M := (D.liftKaehlerDifferential.liftBaseChange C).comp r
  let E : Derivation R C M := L.compDer (KaehlerDifferential.D R C)
  refine ⟨E, fun b => ?_⟩
  have hD : KaehlerDifferential.mapBaseChange R B C
      (1 ⊗ₜ[B] KaehlerDifferential.D R B b) =
        KaehlerDifferential.D R C (algebraMap B C b) := by
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  have hret := LinearMap.congr_fun hr (1 ⊗ₜ[B] KaehlerDifferential.D R B b)
  change D.liftKaehlerDifferential.liftBaseChange C
    (r (KaehlerDifferential.D R C (algebraMap B C b))) = D b
  rw [← hD, show r (KaehlerDifferential.mapBaseChange R B C
      (1 ⊗ₜ[B] KaehlerDifferential.D R B b)) = 1 ⊗ₜ[B] KaehlerDifferential.D R B b from hret]
  simp only [LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]

/-- The canonical restriction of actual derivations is surjective. -/
theorem restriction_surjective [Algebra.FormallySmooth B C] :
    Function.Surjective (fun E : Derivation R C M => E.compAlgebraMap B) := by
  intro D
  obtain ⟨E, hE⟩ := exists_extension R B C M D
  refine ⟨E, Derivation.ext fun b => ?_⟩
  exact hE b

end M9Native.FormallySmoothDerivationExtension

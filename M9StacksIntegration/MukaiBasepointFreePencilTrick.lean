module

public import M9StacksIntegration.MukaiPencilQuotient
public import M9StacksIntegration.CompleteEvaluationGeneration
public import M9StacksIntegration.MukaiRecognitionHomBound
public import M9StacksIntegration.MukaiTensorLineCancellation

/-!
# The actual basepoint-free pencil-trick H0 inequality

The generating pencil is the actual evaluation of the original two
sections. Its native kernel is identified with the genuine dual line
using the proved pencil-kernel dual isomorphism and native double duality.
Tensoring its actual short exact sequence and applying H0 exactness gives
the bound, with the original structural K action throughout.

The complete-basis wrapper takes actual epimorphic evaluation. It does
not produce basepoint freeness for a pencil with a moving part.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiBasepointFreePencilTrick

variable {X : Scheme.{u}}

/-- The original pencil evaluation and its literal native kernel. -/
def pencilSequence (ξ : X.Modules) (t : ULift.{u} (Fin 2) → ξ.sections) :
    ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (MukaiPencilQuotient.pencilEvaluation ξ t))
    (MukaiPencilQuotient.pencilEvaluation ξ t) (kernel.condition _)

theorem pencilSequence_shortExact (ξ : X.Modules)
    (t : ULift.{u} (Fin 2) → ξ.sections)
    (hp : Epi (MukaiPencilQuotient.pencilEvaluation ξ t)) :
    (pencilSequence ξ t).ShortExact :=
  { exact := ShortComplex.exact_kernel _
    mono_f := by
      change Mono (kernel.ι (MukaiPencilQuotient.pencilEvaluation ξ t))
      infer_instance
    epi_g := hp }

/-- The actual kernel line is the dual of the original generating pencil.
Neither its rank nor this isomorphism is supplied as an input. -/
def pencilKernelIsoDual (ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (t : ULift.{u} (Fin 2) → ξ.sections)
    (hp : Epi (MukaiPencilQuotient.pencilEvaluation ξ t)) :
    kernel (MukaiPencilQuotient.pencilEvaluation ξ t) ≅ dualSheaf ξ := by
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (kernel (MukaiPencilQuotient.pencilEvaluation ξ t)) :=
    (MukaiPencilQuotient.pencilKernel_rank ξ t hp).isFiniteLocallyFree
  letI : IsIso (toDoubleDual (kernel (MukaiPencilQuotient.pencilEvaluation ξ t))) :=
    isIso_toDoubleDual_of_isFiniteLocallyFree _
  exact asIso (toDoubleDual (kernel (MukaiPencilQuotient.pencilEvaluation ξ t))) ≪≫
    (MukaiPencilQuotient.dualIso (MukaiPencilQuotient.pencilKernelDualIso ξ t hp)).symm

/-- The literal tensor of the original evaluation sequence. -/
def tensorSequence (B ξ : X.Modules) (t : ULift.{u} (Fin 2) → ξ.sections) :
    ShortComplex X.Modules := by
  letI := MukaiCupAlternating.tensorRight_additive B
  exact (pencilSequence ξ t).map (MukaiCupAlternating.tensorRight B)

theorem tensorSequence_shortExact (B ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    (t : ULift.{u} (Fin 2) → ξ.sections)
    (hp : Epi (MukaiPencilQuotient.pencilEvaluation ξ t)) :
    (tensorSequence B ξ t).ShortExact := by
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X B
  let := MukaiCupAlternating.tensorRight_additive B
  let : PreservesFiniteLimits (MukaiCupAlternating.tensorRight B) :=
    (MukaiCupAlternating.tensorRight_exact B
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree B 1)).1
  let : PreservesFiniteColimits (MukaiCupAlternating.tensorRight B) :=
    (MukaiCupAlternating.tensorRight_exact B
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree B 1)).2
  exact (pencilSequence_shortExact ξ t hp).map_of_exact (MukaiCupAlternating.tensorRight B)

variable (K : Type u) [Field K] (f : X ⟶ Spec (.of K))

/-- Actual maps from the original free pencil are the original pair of H0
classes, with the scalar action induced by the original structure map. -/
def pencilFreeHomEquiv (B : X.Modules) :
    letI := modulesLinearOverField K f
    (MukaiPencilQuotient.pencilFree X ⟶ B) ≃ₗ[K]
      (ULift.{u} (Fin 2) → (structureModule X ⟶ B)) := by
  letI := modulesLinearOverField K f
  refine
    { toFun := fun g j => SheafOfModules.ιFree j ≫ g
      invFun := fun v => Sigma.desc v
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro g h
    funext j
    simp only [Pi.add_apply, Preadditive.comp_add]
  · intro c g
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply, Linear.comp_smul]
  · intro g
    apply Sigma.hom_ext
    intro j
    simp [SheafOfModules.ιFree]
  · intro v
    funext j
    simp [SheafOfModules.ιFree]

/-- The true H0 of the actual free-pencil tensor has twice the original H0. -/
theorem free_tensor_H0_finrank [IsProper f] (B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] :
    Module.finrank K (cohomologyOverField K f
      (tensor (MukaiPencilQuotient.pencilFree X) B) 0) =
      2 * Module.finrank K (cohomologyOverField K f B 0) := by
  let := modulesLinearOverField K f
  let := MukaiPencilQuotient.pencilFree_rank X
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X B
  let := MukaiRecognitionHomBound.finite_bundle_H0 K f B 1
  let e : (dualSheaf (MukaiPencilQuotient.pencilFree X) ⟶ B) ≃ₗ[K]
      (ULift.{u} (Fin 2) → cohomologyOverField K f B 0) :=
    (Linear.homCongr K (dualSheafFreeIso X (ULift.{u} (Fin 2))) (Iso.refl B)).trans
      ((pencilFreeHomEquiv K f B).trans
        (LinearEquiv.piCongrRight fun _ => unitHomLinearEquivCohomologyZero K f B))
  rw [← (MukaiRecognitionHomBound.homDualTensorH0Equiv K f
    (MukaiPencilQuotient.pencilFree X) B 2).finrank_eq,
    e.finrank_eq, Module.finrank_pi_fintype]
  simp

/-- The genuine pencil-trick inequality follows from the actual tensor
evaluation sequence. No kernel identification or H0 bound is an input. -/
theorem tensor_H0_inequality [IsProper f] (B ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (t : ULift.{u} (Fin 2) → ξ.sections)
    (hp : Epi (MukaiPencilQuotient.pencilEvaluation ξ t)) :
    2 * Module.finrank K (cohomologyOverField K f B 0) ≤
      Module.finrank K (cohomologyOverField K f (tensor B ξ) 0) +
        Module.finrank K (cohomologyOverField K f (tensor B (dualSheaf ξ)) 0) := by
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X B
  let := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X ξ
  let := MukaiPencilQuotient.pencilFree_rank X
  let := MukaiPencilQuotient.pencilKernel_rank ξ t hp
  let := MukaiCupAlternating.tensorRight_additive B
  let : Module.Finite K (cohomologyOverField K f
      (tensorSequence B ξ t).X₁ 0) :=
    MukaiRecognitionHomBound.finite_tensor_H0 K f
      (kernel (MukaiPencilQuotient.pencilEvaluation ξ t)) B 1 1
  let : Module.Finite K (cohomologyOverField K f
      (tensorSequence B ξ t).X₂ 0) :=
    MukaiRecognitionHomBound.finite_tensor_H0 K f (MukaiPencilQuotient.pencilFree X) B 2 1
  let : Module.Finite K (cohomologyOverField K f
      (tensorSequence B ξ t).X₃ 0) :=
    MukaiRecognitionHomBound.finite_tensor_H0 K f ξ B 1 1
  have hb := MukaiBundleUniqueness.finrank_H0_le_add K f
    (tensorSequence_shortExact B ξ t hp)
  change Module.finrank K (cohomologyOverField K f
      (tensor (MukaiPencilQuotient.pencilFree X) B) 0) ≤
    Module.finrank K (cohomologyOverField K f
      (tensor (kernel (MukaiPencilQuotient.pencilEvaluation ξ t)) B) 0) +
    Module.finrank K (cohomologyOverField K f (tensor ξ B) 0) at hb
  have hker := (cohomologyOverFieldIso K f
    (tensorIso (pencilKernelIsoDual ξ t hp) (Iso.refl B) ≪≫
      MukaiTensorLineCancellation.tensorSwap (dualSheaf ξ) B) 0).toLinearEquiv.finrank_eq
  have hright := (cohomologyOverFieldIso K f
    (MukaiTensorLineCancellation.tensorSwap ξ B) 0).toLinearEquiv.finrank_eq
  rw [free_tensor_H0_finrank K f B, hker, hright] at hb
  omega

/-- The complete original cohomology basis gives the very same native
pencil evaluation, with its original two free generators. -/
theorem pencilEvaluation_basisSections (ξ : X.Modules)
    (bξ : Module.Basis (ULift.{u} (Fin 2)) K (cohomologyOverField K f ξ 0)) :
    MukaiPencilQuotient.pencilEvaluation ξ
        (CompleteEvaluationGeneration.basisSections f ξ bξ) =
      CompleteEvaluationGeneration.basisEvaluation f ξ bξ := rfl

/-- The requested complete-basis BPF endpoint on the original actual lines.
Epimorphic evaluation is explicit; no moving-part or no5 assertion is made. -/
theorem complete_basis_H0_inequality [IsProper f] (B ξ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ξ]
    (bξ : Module.Basis (ULift.{u} (Fin 2)) K (cohomologyOverField K f ξ 0))
    (hp : Epi (CompleteEvaluationGeneration.basisEvaluation f ξ bξ)) :
    2 * Module.finrank K (cohomologyOverField K f B 0) ≤
      Module.finrank K (cohomologyOverField K f (tensor B ξ) 0) +
        Module.finrank K (cohomologyOverField K f (tensor B (dualSheaf ξ)) 0) := by
  have he : Epi (MukaiPencilQuotient.pencilEvaluation ξ
      (CompleteEvaluationGeneration.basisSections f ξ bξ)) :=
    (congrArg (fun g : MukaiPencilQuotient.pencilFree X ⟶ ξ => Epi g)
      (pencilEvaluation_basisSections K f ξ bξ)).mpr hp
  exact tensor_H0_inequality K f B ξ (CompleteEvaluationGeneration.basisSections f ξ bξ) he

end M9Native.MukaiBasepointFreePencilTrick

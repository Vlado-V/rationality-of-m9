module

public import M9StacksIntegration.MukaiGeneratedCartierImage
public import M9StacksIntegration.MukaiGeneratedQuotient
public import M9StacksIntegration.MukaiDualSpanNoUnit

/-!
# No trivial quotient of the actual Cartier generated image

The literal ideal relation and one-dimensional constants force every
map from the generated image to O_X to vanish. This supplies the
two-section quotient bound in the four-section case.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundle

universe u

namespace M9Native.MukaiGeneratedCartierImage

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k))
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
include f

theorem end_structure_finrank_one :
    letI := modulesLinearOverField k f
    Module.finrank k (structureModule X ⟶ structureModule X) = 1 := by
  letI := modulesLinearOverField k f
  exact (unitHomLinearEquivCohomologyZero k f (structureModule X)).finrank_eq.trans
    (finrank_cohomologyOverField_unit_zero_eq_one f)

theorem id_structure_ne_zero : (𝟙 (structureModule X)) ≠ 0 := by
  letI := modulesLinearOverField k f
  intro hid
  have hs : Subsingleton (structureModule X ⟶ structureModule X) := ⟨by
    intro a b
    calc
      a = (𝟙 (structureModule X)) ≫ a := (Category.id_comp a).symm
      _ = 0 := by rw [hid, zero_comp]
      _ = (𝟙 (structureModule X)) ≫ b := by rw [hid, zero_comp]
      _ = b := Category.id_comp b⟩
  letI := hs
  have hz : Module.finrank k (structureModule X ⟶ structureModule X) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hone := end_structure_finrank_one f
  omega

/-- Invertibility of the actual ideal and nonzero constants imply its
inclusion is a nonzero morphism. -/
theorem idealInclusion_ne_zero (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.Divisors.idealSheafInclusion D ≠ 0 := by
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (Stacks.Divisors.negativeTwist' D) :=
    Stacks.Divisors.isTensorInvertible_negativeTwist D
  letI : Mono (Stacks.Divisors.idealSheafInclusion D) :=
    Stacks.ClosedImmersion.mono_idealSheafι _
  intro hz
  have hI : IsZero (Stacks.Divisors.negativeTwist' D) :=
    IsZero.of_mono_eq_zero (Stacks.Divisors.idealSheafInclusion D) hz
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
    (Stacks.Divisors.invertibleSheaf' D)
  letI : T.Additive := by dsimp [T]; infer_instance
  have hT := T.map_isZero hI
  have hO : IsZero (structureModule X) :=
    hT.of_iso (Stacks.SheafOfModules.Scheme.evaluationIso X
      (Stacks.Divisors.negativeTwist' D)).symm
  exact id_structure_ne_zero f (hO.eq_of_src _ _)

/-- The generated image in Q(D) has no map to O_X when Q has none. -/
theorem hom_structure_eq_zero (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (Q : X.Modules)
    (hQ : ∀ v : Q ⟶ structureModule X, v = 0)
    (a : structureModule X ⟶ Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D))
    (v : MukaiGeneratedImage.generatedImage (inclusion D Q) a ⟶ structureModule X) :
    v = 0 := by
  letI := modulesLinearOverField k f
  exact MukaiGeneratedImage.hom_unit_eq_zero (k := k) (inclusion D Q) a
    hQ (end_structure_finrank_one f) (id_structure_ne_zero f)
    (Stacks.Divisors.idealSheafInclusion D) (idealInclusion_ne_zero f D)
    (contraction D Q a) (ideal_relation D Q a) v

end M9Native.MukaiGeneratedCartierImage


module

public import M9StacksIntegration.MukaiConormalBundle
public import M9StacksIntegration.LagrangianTranslatedCharts
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge

/-!
# The actual primitive-Plücker conormal exact sequence

This uses the native immersion conormal sequence and its actual
categorical-ideal comparison. The last term is the literal relative
differential sheaf of the actual LG structure morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalSequence

variable (K : Type u) [Field K] [CharZero K]

abbrev ambientProjection :=
  projectiveSpaceOfModuleToSpec K (Module.Dual K (LagrangianField.Primitive K))

theorem primitivePlucker_projection :
    LagrangianPluckerLinear.primitivePlucker K ≫ ambientProjection K =
      LagrangianGrassmannian.projection K := by
  unfold LagrangianPluckerLinear.primitivePlucker
  rw [Category.assoc]
  change LagrangianPlucker.primitivePlucker K ≫
    ((basisProjectiveSpaceIso (LagrangianPluckerLinear.primitiveBasis14 K).dualBasis).hom ≫
      projectiveSpaceOfModuleToSpec K _) = _
  rw [basisProjectiveSpaceIso_hom_comp_toSpec]
  exact LagrangianPlucker.primitivePlucker_projection K

abbrev nativeSequence := Stacks.ConormalSequenceRight.conormalShortComplex
  (LagrangianPluckerLinear.primitivePlucker K) (ambientProjection K)

/-- The native sequence uses the sectionwise defining ideal; the
original conormal sheaf uses the categorical ideal. This is their
proved native comparison, not a definitional identification. -/
def sourceIso : (nativeSequence K).X₁ ≅ MukaiConormalBundle.conormal K :=
  Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge
    (LagrangianPluckerLinear.primitivePlucker K)

def targetIso : (nativeSequence K).X₃ ≅
    Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K) :=
  eqToIso (congrArg Scheme.Hom.relativeDifferentials (primitivePlucker_projection K))

def inclusion : MukaiConormalBundle.conormal K ⟶ (nativeSequence K).X₂ :=
  (sourceIso K).inv ≫ (nativeSequence K).f

def differential : (nativeSequence K).X₂ ⟶
    Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K) :=
  (nativeSequence K).g ≫ (targetIso K).hom

theorem inclusion_comp_differential : inclusion K ≫ differential K = 0 := by
  simp [inclusion, differential, Category.assoc]

def sequence : ShortComplex (LagrangianGrassmannian.space K).Modules :=
  ShortComplex.mk (inclusion K) (differential K) (inclusion_comp_differential K)

def comparisonIso : nativeSequence K ≅ sequence K :=
  ShortComplex.isoMk (sourceIso K) (Iso.refl _) (targetIso K)
    (by simp [sequence, inclusion]) (by simp [sequence, differential])

variable [IsAlgClosed K]

theorem sequence_shortExact : (sequence K).ShortExact := by
  have hsm : Smooth (LagrangianPluckerLinear.primitivePlucker K ≫ ambientProjection K) := by
    rw [primitivePlucker_projection]
    infer_instance
  exact ShortComplex.shortExact_of_iso (comparisonIso K)
    (Stacks.ConormalSequenceRight.conormalShortComplex_shortExact _ _ hsm)

instance inclusion_mono : Mono (inclusion K) := (sequence_shortExact K).mono_f

instance differential_epi : Epi (differential K) := (sequence_shortExact K).epi_g

end M9Native.MukaiConormalSequence

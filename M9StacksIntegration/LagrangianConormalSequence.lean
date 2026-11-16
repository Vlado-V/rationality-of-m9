module

public import M9StacksIntegration.LagrangianIntegral
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge

/-!
# The actual LG-in-Grassmannian conormal sequence

The maps are the literal native conormal differential and relative
Kähler differential of the original closed inclusion. Smoothness of
the original LG, proved from its actual charts, gives short exactness.
No conormal rank, regular-section, or cotangent identification is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian

variable (K : Type u) [Field K]

/-- The actual native sequence I/I² → i*ΩGr → ΩLG. -/
abbrev conormalSequence :=
  Stacks.ConormalSequenceRight.conormalShortComplex
    (inclusion K) (grassmannianProjection K)

/-- This comparison is the genuine native bridge between the two
categorical/sectionwise defining-ideal constructions. -/
def conormalSequence_sourceIso :
    (conormalSequence K).X₁ ≅ Stacks.Conormal.conormalSheaf (inclusion K) :=
  Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge (inclusion K)

theorem conormalSequence_shortExact : (conormalSequence K).ShortExact := by
  have hsm : Smooth (inclusion K ≫ grassmannianProjection K) :=
    inferInstanceAs (Smooth (projection K))
  exact Stacks.ConormalSequenceRight.conormalShortComplex_shortExact
    (inclusion K) (grassmannianProjection K) hsm

instance conormalSequence_f_mono : Mono (conormalSequence K).f :=
  (conormalSequence_shortExact K).mono_f

instance conormalSequence_g_epi : Epi (conormalSequence K).g :=
  (conormalSequence_shortExact K).epi_g

end M9Native.LagrangianDegree

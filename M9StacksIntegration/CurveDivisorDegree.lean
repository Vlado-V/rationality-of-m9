module

public import M9StacksIntegration.CurveDivisorSections
public import M9StacksIntegration.MukaiPencilDegreeBounds

/-!
# Native degree and sections after an actual divisor twist

The degree of the original ideal twist is calculated from the actual
evaluation pairing of its ideal and divisor sheaves. Low-degree
effective divisor sheaves have exactly one section on a nonpentagonal
curve, using the original no-degree-five-pencil condition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.CurveDivisorDegree

open CategoryTheory AlgebraicGeometry
open M9Native.CurveDivisorSections
open Stacks.Divisors (IsEffectiveCartierDivisor)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The native negative twist has degree minus the length of the actual
effective divisor, as calculated through its actual evaluation pairing. -/
theorem negativeTwist_degree (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    invertibleCurveDegree k f hdim (Stacks.Divisors.negativeTwist' D) =
      -(Module.finrank k Γ(D.subscheme, ⊤) : ℤ) := by
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  let I : X.Modules := Stacks.Divisors.negativeTwist' D
  let O : X.Modules := Stacks.Divisors.invertibleSheaf' D
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property O :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property I :=
    Stacks.Divisors.isInvertible_negativeTwist D
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property I :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ I inferInstance
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Scheme.Modules.tensorObj O I) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
      X.ringCatSheaf.property O I
  let e : Scheme.Modules.tensorObj O I ≅ SheafOfModules.unit X.ringCatSheaf :=
    Stacks.SheafOfModules.Scheme.evaluationIso X I
  have hsum := invertibleCurveDegree_tensorSheaf_eq_add k f hdim O I
  have he := invertibleCurveDegree_eq_of_iso k f hdim e
  have hunit := invertibleCurveDegree_unit_eq_zero k f hdim
  have hO : invertibleCurveDegree k f hdim O =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) :=
    invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D
  change invertibleCurveDegree k f hdim (Scheme.Modules.tensorObj O I) =
    invertibleCurveDegree k f hdim O + invertibleCurveDegree k f hdim I at hsum
  change invertibleCurveDegree k f hdim I = _
  omega

/-- Twisting the actual line bundle down by the actual divisor subtracts
that divisor's length from its original native degree. -/
theorem twistDown_degree (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    invertibleCurveDegree k f hdim (twistDown D L) =
      invertibleCurveDegree k f hdim L - (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) := by
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have hn := negativeTwist_degree f hdim D
  have hs := invertibleCurveDegree_tensorSheaf_eq_add k f hdim
    (Stacks.Divisors.negativeTwist' D) L
  change invertibleCurveDegree k f hdim (twistDown D L) =
    invertibleCurveDegree k f hdim (Stacks.Divisors.negativeTwist' D) +
      invertibleCurveDegree k f hdim L at hs
  rw [hs, hn]
  ring

/-- The original regular canonical section embeds the structure sheaf,
so the actual effective-divisor sheaf has at least one section. -/
theorem one_le_divisorSheaf_h0
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    1 ≤ Module.finrank k (cohomologyOverField k f (Stacks.Divisors.invertibleSheaf' D) 0) := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.invertibleSheaf' D) := Stacks.Divisors.invertibleSheaf_isInvertible D
  let : Mono (Stacks.Divisors.canonicalHom D) := Stacks.Divisors.canonicalSection_isRegular D
  let := invertible_cohomology_zero_finite f (Stacks.Divisors.invertibleSheaf' D)
  have hi := M9StacksIntegration.LinearSeriesAddEffectiveDivisor.injective_cohomology_zero_of_mono
    f (Stacks.Divisors.canonicalHom D)
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (cohomologyOverFieldMap k f (Stacks.Divisors.canonicalHom D) 0).hom) hi
  change Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) ≤
    Module.finrank k (cohomologyOverField k f (Stacks.Divisors.invertibleSheaf' D) 0) at hle
  rw [finrank_cohomologyOverField_unit_zero_eq_one f] at hle
  exact hle

/-- The divisor sheaf has exactly one actual section when its degree is
at most five on an actual nonpentagonal smooth proper curve. -/
theorem divisorSheaf_h0_eq_one_of_degree_le_five [IsAlgClosed k] [IsCurve k f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hdeg : invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) ≤ 5) :
    Module.finrank k (cohomologyOverField k f (Stacks.Divisors.invertibleSheaf' D) 0) = 1 := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.invertibleSheaf' D) := Stacks.Divisors.invertibleSheaf_isInvertible D
  have hlow := one_le_divisorSheaf_h0 f D
  by_contra hne
  have htwo : 2 ≤ Module.finrank k
      (cohomologyOverField k f (Stacks.Divisors.invertibleSheaf' D) 0) := by omega
  have h := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp
    (Stacks.Divisors.invertibleSheaf' D) htwo
  omega

end M9Native.CurveDivisorDegree

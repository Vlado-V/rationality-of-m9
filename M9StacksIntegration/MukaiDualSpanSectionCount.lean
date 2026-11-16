module

public import M9StacksIntegration.MukaiDualSpanDual
public import M9StacksIntegration.MukaiFilteredVanishing
public import M9StacksIntegration.CurveDivisorDegree

/-!
# Section count from the actual divisor sequence

For the actual sequence `0 → O(D) → Qβ → β(-D) → 0` the native
cohomology exact sequence gives the upper bound on `h⁰(Qβ)`. The lower
bound comes independently from the actual dual net evaluation sequence.
The same actual filtration proves the required inverse-twist vanishing.

This composition lemma consumes the geometric length-two divisor
sequence. It does not assert the still separate existence of that
divisor sequence and is not presented as a completed Mukai theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.MukaiDualSpanSectionCount

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiDualSpanSections M9Native.MukaiDualSpanDual
open M9Native.CurveDivisorSections M9Native.CurveDivisorDegree

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual line-bundle filtration bounds sections of the actual
dual span. Properness and the previously derived ranks supply every
finite-dimensionality hypothesis. -/
theorem dualSpan_h0_le_of_exact_line_filtration
    (f : X ⟶ Spec (.of k)) [IsProper f] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property B]
    (i : A ⟶ dualSpan β s) (p : dualSpan β s ⟶ B) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact) :
    Module.finrank k (cohomologyOverField k f (dualSpan β s) 0) ≤
      Module.finrank k (cohomologyOverField k f A 0) +
        Module.finrank k (cohomologyOverField k f B 0) := by
  let := dualSpan_rank β s hgen
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (dualSpan β s) 2
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (dualSpan β s).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X _
  let := finiteDimensional_cohomologyOverField_of_isProper k f (dualSpan β s) 0
  let := invertible_cohomology_zero_finite f B
  obtain ⟨_δ, hi, he, _hd, _hd'⟩ := exists_cohomologyOverField_longExactSequence k f hS
  let a := (cohomologyOverFieldMap k f i 0).hom
  let q := (cohomologyOverFieldMap k f p 0).hom
  have ha : Function.Injective a := hi
  have hex : Function.Exact a q := he 0
  have hr := q.finrank_range_add_finrank_ker
  rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj ha] at hr
  have hle := Submodule.finrank_le (LinearMap.range q)
  omega

/-- The two conclusions of Mukai Lemma 5.1 follow from its actual
line-bundle filtration; neither conclusion is supplied as input. The
geometric divisor construction supplies the outer dimensions and degrees. -/
theorem count_and_vanishing_of_exact_line_filtration
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) (α β A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property B]
    (hα : invertibleCurveDegree k f hdim α = 8)
    (hβ : invertibleCurveDegree k f hdim β = 8)
    (hA : invertibleCurveDegree k f hdim A = 2)
    (hB : invertibleCurveDegree k f hdim B = 6)
    (hA0 : Module.finrank k (cohomologyOverField k f A 0) = 1)
    (hB0 : Module.finrank k (cohomologyOverField k f B 0) = 2)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    (i : A ⟶ dualSpan β s) (p : dualSpan β s ⟶ B) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk (C := X.Modules) i p w).ShortExact) :
    Module.finrank k (cohomologyOverField k f (dualSpan β s) 0) = 3 ∧
      Subsingleton (cohomologyOverField k f
        (Scheme.Modules.tensorObj (dualSheaf α) (dualSpan β s)) 0) := by
  have hupper := dualSpan_h0_le_of_exact_line_filtration f β s hgen A B i p w hS
  have hupper' : Module.finrank k (cohomologyOverField k f (dualSpan β s) 0) ≤ 3 := by omega
  have hβpos : 0 < invertibleCurveDegree k f hdim β := by omega
  have hlower := three_le_dualSpan_cohomology_zero_finrank f hdim β b s hgen
    hβpos
  refine ⟨le_antisymm hupper' hlower, ?_⟩
  exact MukaiFilteredVanishing.dualTwist_cohomology_zero_subsingleton_of_degrees_two_six_eight
    f hdim α (S := ShortComplex.mk (C := X.Modules) i p w) hS hα hA hB

end M9Native.MukaiDualSpanSectionCount

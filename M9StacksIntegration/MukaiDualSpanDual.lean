module

public import M9StacksIntegration.MukaiDualSpanSections
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# The dual of the actual dual span

The kernel of a generating line-bundle net is finite locally free of rank
two. Its canonical double-dual map is therefore invertible, identifying
the dual of the constructed dual span with the original evaluation
kernel. Completeness then proves that this actual dual has no sections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.MukaiDualSpanDual

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiDualSpanSections

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Canonical reflexivity of the original finite locally free evaluation
kernel identifies `Qβ∨` with that original kernel. -/
def dualSpanDualIsoKernel (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s)) :
    dualSheaf (dualSpan β s) ≅ evaluationKernel β s := by
  letI := evaluationKernel_rank β s hgen
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (evaluationKernel β s) 2
  letI := isIso_toDoubleDual_of_isFiniteLocallyFree (evaluationKernel β s)
  exact (asIso (toDoubleDual (evaluationKernel β s))).symm

/-- The actual dual of the dual span of a complete generating net has
zero native degree-zero cohomology. -/
theorem completeDualSpanDual_cohomology_zero_subsingleton
    (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hgen : Epi (netEvaluation β (completeNetSections f β b))) :
    Subsingleton (cohomologyOverField k f
      (dualSheaf (dualSpan β (completeNetSections f β b))) 0) := by
  let hkernel := completeNetKernel_cohomology_zero_subsingleton f β b hgen
  let e := (cohomologyOverFieldIso k f
    (dualSpanDualIsoKernel β (completeNetSections f β b) hgen) 0).toLinearEquiv
  exact ⟨fun a c => e.injective (hkernel.elim (e a) (e c))⟩

theorem completeDualSpanDual_cohomology_zero_finrank
    (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hgen : Epi (netEvaluation β (completeNetSections f β b))) :
    Module.finrank k (cohomologyOverField k f
      (dualSheaf (dualSpan β (completeNetSections f β b))) 0) = 0 := by
  let := completeDualSpanDual_cohomology_zero_subsingleton f β b hgen
  exact Module.finrank_zero_of_subsingleton

/-- The actual free middle term in the dual evaluation sequence still
has three global sections, through its proved free-dual isomorphism. -/
theorem dualNetFree_cohomology_zero_finrank
    (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (β : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0)) :
    Module.finrank k (cohomologyOverField k f (dualSheaf (netFree X)) 0) = 3 :=
  (finrank_cohomologyOverField_eq_of_iso k f (dualNetFreeIso X) 0).trans
    (netFree_cohomology_zero_finrank f β b)

/-- The lower bound in Mukai Lemma 5.1(1) follows from the actual dual
evaluation sequence and positivity of the original line-bundle degree.
Finite dimensionality is obtained from properness and the proved rank,
and is not an additional hypothesis about the constructed dual span. -/
theorem three_le_dualSpan_cohomology_zero_finrank
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    (hdeg : 0 < invertibleCurveDegree k f hdim β) :
    3 ≤ Module.finrank k (cohomologyOverField k f (dualSpan β s) 0) := by
  let := dualSpan_rank β s hgen
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (dualSpan β s) 2
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (dualSpan β s).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X _
  let := finiteDimensional_cohomologyOverField_of_isProper k f (dualSpan β s) 0
  let hkernel := dual_cohomology_zero_subsingleton_of_positive_degree f hdim β hdeg
  obtain ⟨w, hS⟩ := dualEvaluationSequence_shortExact β s hgen
  obtain ⟨_δ, _hi, he, _hd, _hd'⟩ := exists_cohomologyOverField_longExactSequence k f hS
  let a := (cohomologyOverFieldMap k f (dualMap (netEvaluation β s)) 0).hom
  let q := (cohomologyOverFieldMap k f (dualMap (evaluationKernelInclusion β s)) 0).hom
  have hex : Function.Exact a q := he 0
  have hq : Function.Injective q := by
    intro x y hxy
    have hzero : q (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨v, hv⟩ := (hex (x - y)).mp hzero
    have hv0 : v = 0 := hkernel.elim _ _
    exact sub_eq_zero.mp (hv.symm.trans (by rw [hv0, a.map_zero]))
  calc
    3 = Module.finrank k (cohomologyOverField k f (dualSheaf (netFree X)) 0) :=
      (dualNetFree_cohomology_zero_finrank f β b).symm
    _ ≤ Module.finrank k (cohomologyOverField k f (dualSpan β s) 0) :=
      LinearMap.finrank_le_finrank_of_injective hq

end M9Native.MukaiDualSpanDual

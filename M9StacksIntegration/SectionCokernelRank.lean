module

public import M9StacksIntegration.SectionCokernelDualSequence
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral

/-!
# The actual rank and locally split cokernel of an epimorphic dual section

The kernel's rank is the native rank calculation for an actual
epimorphism. Actual duality then supplies the categorical cokernel,
its rank, and the genuine local splitting. The final field-nonvanishing
wrapper derives the dual epimorphism independently by Nakayama.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionCokernelLocallyFree

variable {X : Scheme.{u}}

theorem dualKernel_rank_of_dualMap_epi {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hq : Epi (dualMap s)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualKernel s) (r-1) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
    (dualMap s) hq r 1 (isFiniteLocallyFreeOfRank_dualSheaf H r hH)
    (isFiniteLocallyFreeOfRank_dualSheaf (unitModule X) 1 (unitModule_rank X))

theorem mono_of_dualMap_epi {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hq : Epi (dualMap s)) : Mono s :=
  (dualKernelSequence_shortExact_of_dualMap_epi s r hH hq).mono_f

theorem cokernel_rank_of_dualMap_epi {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hq : Epi (dualMap s)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel s) (r-1) :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (cokernelIsoDualKernel_of_dualMap_epi s r hH hq).symm
    (isFiniteLocallyFreeOfRank_dualSheaf (dualKernel s) (r-1)
      (dualKernel_rank_of_dualMap_epi s r hH hq))

/-- The actual cokernel sequence, with its original section as left map. -/
abbrev cokernelSequence {H : X.Modules} (s : unitModule X ⟶ H) : ShortComplex X.Modules :=
  ShortComplex.mk s (cokernel.π s) (cokernel.condition s)

theorem cokernelSequence_shortExact_of_dualMap_epi {H : X.Modules}
    (s : unitModule X ⟶ H) (r : ℕ)
    (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r) (hq : Epi (dualMap s)) :
    (cokernelSequence s).ShortExact := by
  let : Mono s := mono_of_dualMap_epi s r hH hq
  exact { exact := ShortComplex.exact_cokernel s }

theorem cokernelSequence_locally_split_of_dualMap_epi {H : X.Modules}
    (s : unitModule X ⟶ H) (r : ℕ)
    (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r) (hq : Epi (dualMap s)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((cokernelSequence s).map (Scheme.Modules.restrictFunctor U.ι)).Splitting := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel s) :=
    (cokernel_rank_of_dualMap_epi s r hH hq).isFiniteLocallyFree
  exact Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree
    (cokernelSequence s) (cokernelSequence_shortExact_of_dualMap_epi s r hH hq) x

end M9Native.SectionCokernelLocallyFree

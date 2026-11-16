module

public import M9StacksIntegration.SectionCokernelField
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic

/-!
# The actual quotient constructed from an epimorphic dual section

This is the pure sheaf construction. The native kernel theorem is applied
only to an actual epimorphism onto an actual finite locally free sheaf.
Dualizing its genuine exact kernel sequence identifies the actual
cokernel of the original section. No cokernel freeness is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionCokernelLocallyFree

variable {X : Scheme.{u}}

/-- The actual kernel of the actual dual section. -/
abbrev dualKernel {H : X.Modules} (s : unitModule X ⟶ H) : X.Modules :=
  kernel (dualMap s)

/-- The actual quotient map obtained from native double duality. -/
def dualKernelProjection {H : X.Modules} (s : unitModule X ⟶ H) : H ⟶ dualSheaf (dualKernel s) :=
  toDoubleDual H ≫ dualMap (kernel.ι (dualMap s))

theorem dualKernelProjection_comp {H : X.Modules} (s : unitModule X ⟶ H) :
    s ≫ dualKernelProjection s = 0 := by
  have wd : dualMap (dualMap s) ≫ dualMap (kernel.ι (dualMap s)) = 0 :=
    (dualMap_comp (kernel.ι (dualMap s)) (dualMap s)).symm.trans
      ((congrArg dualMap (kernel.condition (dualMap s))).trans
        (dualMap_zero_map (dualKernel s) (dualSheaf (unitModule X))))
  change s ≫ (toDoubleDual H ≫ dualMap (kernel.ι (dualMap s))) = 0
  rw [← Category.assoc, toDoubleDual_naturality, Category.assoc]
  exact (congrArg (fun a => toDoubleDual (unitModule X) ≫ a) wd).trans (comp_zero)

def dualKernelSequence {H : X.Modules} (s : unitModule X ⟶ H) : ShortComplex X.Modules :=
  ShortComplex.mk s (dualKernelProjection s) (dualKernelProjection_comp s)

theorem dualKernel_isFiniteLocallyFree {H : X.Modules} (s : unitModule X ⟶ H)
    (hH : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H) (hq : Epi (dualMap s)) :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (dualKernel s) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi (dualMap s) hq
    (isFiniteLocallyFree_dualSheaf H hH)
    (isFiniteLocallyFreeOfRank_dualSheaf (unitModule X) 1 (unitModule_rank X)).isFiniteLocallyFree

/-- Dualizing the genuine finite-locally-free kernel sequence gives the
original section as the left map, by native double-dual naturality. -/
theorem dualKernelSequence_shortExact_of_dualMap_epi {H : X.Modules}
    (s : unitModule X ⟶ H) (r : ℕ)
    (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r) (hq : Epi (dualMap s)) :
    (dualKernelSequence s).ShortExact := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H := hH.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (unitModule X) :=
    (unitModule_rank X).isFiniteLocallyFree
  let : IsIso (toDoubleDual H) := isIso_toDoubleDual_of_isFiniteLocallyFree H
  let : IsIso (toDoubleDual (unitModule X)) :=
    isIso_toDoubleDual_of_isFiniteLocallyFree (unitModule X)
  have hK := dualKernel_isFiniteLocallyFree s hH.isFiniteLocallyFree hq
  have hDH := (isFiniteLocallyFreeOfRank_dualSheaf H r hH).isFiniteLocallyFree
  have hDU := (isFiniteLocallyFreeOfRank_dualSheaf (unitModule X) 1
    (unitModule_rank X)).isFiniteLocallyFree
  let : Epi (dualMap s) := hq
  have hS : (ShortComplex.mk (kernel.ι (dualMap s)) (dualMap s)
      (kernel.condition (dualMap s))).ShortExact := { exact := ShortComplex.exact_kernel _ }
  obtain ⟨w, hd⟩ := exists_dualSheaf_shortExact (kernel.ι (dualMap s)) (dualMap s)
    (kernel.condition (dualMap s)) hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hK)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hDH)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hDU)
  let e : dualKernelSequence s ≅ ShortComplex.mk (dualMap (dualMap s))
      (dualMap (kernel.ι (dualMap s))) w :=
    ShortComplex.isoMk (asIso (toDoubleDual (unitModule X))) (asIso (toDoubleDual H))
      (Iso.refl _) (toDoubleDual_naturality s).symm (by simp [dualKernelSequence, dualKernelProjection])
  exact ShortComplex.shortExact_of_iso e.symm hd

/-- The actual categorical cokernel, identified by its universal property. -/
def cokernelIsoDualKernel_of_dualMap_epi {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hq : Epi (dualMap s)) : cokernel s ≅ dualSheaf (dualKernel s) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel s)
    (dualKernelSequence_shortExact_of_dualMap_epi s r hH hq).gIsCokernel

end M9Native.SectionCokernelLocallyFree

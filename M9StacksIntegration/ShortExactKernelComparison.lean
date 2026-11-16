module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual kernels in two exact rows with the same final quotient

A morphism between two actual short exact rows which is the identity on
the final quotient identifies the kernels of the two original vertical
maps. This supplies the kernel-line comparison when a native flag is
extended by its original tautological-kernel inclusion. No vertical
isomorphism or preserved-kernel conclusion is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.ShortExactKernelComparison

variable {X : Scheme.{u}} {A B A' B' C : X.Modules}
  (i : A ⟶ B) (q : B ⟶ C) (w : i ≫ q = 0)
  (hS : (ShortComplex.mk i q w).ShortExact)
  (i' : A' ⟶ B') (q' : B' ⟶ C) (w' : i' ≫ q' = 0)
  (hS' : (ShortComplex.mk i' q' w').ShortExact)
  (a : A ⟶ A') (b : B ⟶ B')
  (hL : i ≫ b = a ≫ i') (hR : b ≫ q' = q)

/-- The actual original kernel map is an isomorphism, derived from the
true exact rows and the original commuting squares. -/
def kernelIso : kernel a ≅ kernel b := by
  letI : Mono i := hS.mono_f
  letI : Mono i' := hS'.mono_f
  have hkq : kernel.ι b ≫ q = 0 := by
    rw [← hR, ← Category.assoc, kernel.condition, zero_comp]
  let η : kernel b ⟶ A := hS.fIsKernel.lift (KernelFork.ofι (kernel.ι b) hkq)
  have hη : η ≫ i = kernel.ι b :=
    hS.fIsKernel.fac (KernelFork.ofι (kernel.ι b) hkq) WalkingParallelPair.zero
  have hηa : η ≫ a = 0 := by
    apply (cancel_mono i').mp
    rw [Category.assoc, ← hL, ← Category.assoc, hη, kernel.condition, zero_comp]
  let f := kernel.map a b i i' hL.symm
  let g := kernel.lift a η hηa
  have hf : f ≫ kernel.ι b = kernel.ι a ≫ i := kernel.lift_ι _ _ _
  have hg : g ≫ kernel.ι a = η := kernel.lift_ι _ _ _
  refine ⟨f, g, ?_, ?_⟩
  · apply (cancel_mono (kernel.ι a)).mp
    calc
      (f ≫ g) ≫ kernel.ι a = f ≫ η := by rw [Category.assoc, hg]
      _ = kernel.ι a := by
        apply (cancel_mono i).mp
        rw [Category.assoc, hη, hf]
      _ = (𝟙 _) ≫ kernel.ι a := (Category.id_comp _).symm
  · apply (cancel_mono (kernel.ι b)).mp
    calc
      (g ≫ f) ≫ kernel.ι b = g ≫ (kernel.ι a ≫ i) := by rw [Category.assoc, hf]
      _ = η ≫ i := by rw [← Category.assoc, hg]
      _ = kernel.ι b := hη
      _ = (𝟙 _) ≫ kernel.ι b := (Category.id_comp _).symm

theorem kernelIso_hom : (kernelIso i q w hS i' q' w' hS' a b hL hR).hom =
    kernel.map a b i i' hL.symm := rfl

@[reassoc]
theorem kernelIso_hom_ι :
    (kernelIso i q w hS i' q' w' hS' a b hL hR).hom ≫ kernel.ι b =
      kernel.ι a ≫ i := kernel.lift_ι _ _ _

end M9Native.ShortExactKernelComparison

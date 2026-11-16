module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual named quotient and kernel-line compatibility along an epimorphism

For actual modules on a scheme and an actual epimorphism M→Q, the
quotient by each inverse-image subobject is canonically Q/S, preserving
the original quotient maps. These isomorphisms preserve every named
quotient step and therefore identify its actual kernel. Adjacent steps
of the native flag use precisely these kernels as their graded lines.
No flag surrogate, line isomorphism or matrix compatibility is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.FlagQuotientLines

variable {T : Scheme.{u}} {M Q : T.Modules} (π : M ⟶ Q) [Epi π]

theorem exists_iso_of_kernel_eq {L L' : T.Modules} (q : M ⟶ L) (q' : M ⟶ L')
    [Epi q] [Epi q'] (h : kernelSubobject q = kernelSubobject q') :
    ∃ e : L ≅ L', q ≫ e.hom = q' := by
  have key : ∀ {X Y : T.Modules} (p : M ⟶ X) (p' : M ⟶ Y),
      kernelSubobject p ≤ kernelSubobject p' → kernel.ι p ≫ p' = 0 := fun p p' hle => by
    rw [← kernelSubobject_arrow' p, ← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc,
      kernelSubobject_arrow_comp, comp_zero, comp_zero]
  have w := key q q' h.le
  have w' := key q' q h.ge
  refine ⟨⟨Abelian.epiDesc q q' w, Abelian.epiDesc q' q w', ?_, ?_⟩,
    Abelian.comp_epiDesc _ _ _⟩
  · rw [← cancel_epi q, Abelian.comp_epiDesc_assoc, Abelian.comp_epiDesc, Category.comp_id]
  · rw [← cancel_epi q', Abelian.comp_epiDesc_assoc, Abelian.comp_epiDesc, Category.comp_id]

theorem kernel_cokernel_subobject (S : Subobject M) :
    kernelSubobject (cokernel.π S.arrow) = S :=
  le_antisymm
    (Subobject.le_of_comm
      (Abelian.monoLift S.arrow (kernelSubobject (cokernel.π S.arrow)).arrow
        (kernelSubobject_arrow_comp _)) (Abelian.monoLift_comp _ _ _))
    (le_kernelSubobject _ _ (cokernel.condition _))

/-- Literal inverse-image subobject used by the native comap flag. -/
def comapSub (S : Subobject Q) : Subobject M :=
  kernelSubobject (π ≫ cokernel.π S.arrow)

/-- The actual map between quotients by nested original subobjects. -/
def quotientStep {A : T.Modules} {S S' : Subobject A} (h : S ≤ S') :
    cokernel S.arrow ⟶ cokernel S'.arrow :=
  cokernel.desc S.arrow (cokernel.π S'.arrow) (by
    rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero])

@[reassoc]
theorem quotientStep_π {A : T.Modules} {S S' : Subobject A} (h : S ≤ S') :
    cokernel.π S.arrow ≫ quotientStep h = cokernel.π S'.arrow :=
  cokernel.π_desc _ _ _

omit [Epi π] in
/-- Taking these literal inverse images preserves the original inclusions. -/
theorem comapSub_mono {S S' : Subobject Q} (h : S ≤ S') :
    comapSub π S ≤ comapSub π S' := by
  have hc : (π ≫ cokernel.π S.arrow) ≫ quotientStep h = π ≫ cokernel.π S'.arrow := by
    rw [Category.assoc, quotientStep_π]
  exact (kernelSubobject_comp_le (π ≫ cokernel.π S.arrow) (quotientStep h)).trans_eq
    (congrArg (fun f : M ⟶ cokernel S'.arrow => kernelSubobject f) hc)

/-- The actual quotients, normalized by their original quotient maps. -/
def quotientIso (S : Subobject Q) :
    cokernel (comapSub π S).arrow ≅ cokernel S.arrow :=
  Classical.choose (exists_iso_of_kernel_eq
    (cokernel.π (comapSub π S).arrow) (π ≫ cokernel.π S.arrow)
    (by exact kernel_cokernel_subobject (comapSub π S)))

@[reassoc]
theorem quotientIso_π (S : Subobject Q) :
    cokernel.π (comapSub π S).arrow ≫ (quotientIso π S).hom =
      π ≫ cokernel.π S.arrow :=
  Classical.choose_spec (exists_iso_of_kernel_eq
    (cokernel.π (comapSub π S).arrow) (π ≫ cokernel.π S.arrow)
    (by exact kernel_cokernel_subobject (comapSub π S)))

/-- The normalization removes any freedom to insert a quotient automorphism. -/
theorem quotientIso_unique (S : Subobject Q)
    (e : cokernel (comapSub π S).arrow ≅ cokernel S.arrow)
    (he : cokernel.π (comapSub π S).arrow ≫ e.hom = π ≫ cokernel.π S.arrow) :
    e = quotientIso π S := by
  apply Iso.ext
  exact (cancel_epi (cokernel.π (comapSub π S).arrow)).mp
    (he.trans (quotientIso_π π S).symm)

/-- Every original quotient step, not only its source and target objects,
is preserved by the normalized actual quotient isomorphisms. -/
theorem quotientIso_step {S S' : Subobject Q} (h : S ≤ S') :
    quotientStep (comapSub_mono π h) ≫ (quotientIso π S').hom =
      (quotientIso π S).hom ≫ quotientStep h := by
  apply (cancel_epi (cokernel.π (comapSub π S).arrow)).mp
  simp only [quotientStep_π_assoc, quotientIso_π, quotientIso_π_assoc, quotientStep_π]

/-- The actual kernels of corresponding named quotient steps are identified.
For adjacent native flag steps, these are their graded line bundles. -/
def quotientKernelIso {S S' : Subobject Q} (h : S ≤ S') :
    kernel (quotientStep (comapSub_mono π h)) ≅ kernel (quotientStep h) :=
  kernel.mapIso (quotientStep (comapSub_mono π h)) (quotientStep h)
    (quotientIso π S) (quotientIso π S') (quotientIso_step π h)

@[reassoc]
theorem quotientKernelIso_hom_ι {S S' : Subobject Q} (h : S ≤ S') :
    (quotientKernelIso π h).hom ≫ kernel.ι (quotientStep h) =
      kernel.ι (quotientStep (comapSub_mono π h)) ≫ (quotientIso π S).hom :=
  kernel.lift_ι _ _ _

@[reassoc]
theorem quotientKernelIso_inv_ι {S S' : Subobject Q} (h : S ≤ S') :
    (quotientKernelIso π h).inv ≫ kernel.ι (quotientStep (comapSub_mono π h)) =
      kernel.ι (quotientStep h) ≫ (quotientIso π S).inv :=
  kernel.lift_ι _ _ _

/-- The original quotient step is genuinely epimorphic. -/
instance quotientStep_epi {A : T.Modules} {S S' : Subobject A} (h : S ≤ S') :
    Epi (quotientStep h) :=
  epi_of_epi_fac (quotientStep_π h)

/-- The actual kernel/quotient row of a pair of original named quotients. -/
def quotientKernelSequence {A : T.Modules} {S S' : Subobject A} (h : S ≤ S') :
    ShortComplex T.Modules :=
  ShortComplex.mk (kernel.ι (quotientStep h)) (quotientStep h) (kernel.condition _)

/-- This is the genuine short exact row, not an exactness premise. -/
theorem quotientKernelSequence_shortExact {A : T.Modules} {S S' : Subobject A}
    (h : S ≤ S') : (quotientKernelSequence h).ShortExact :=
  { exact := ShortComplex.exact_kernel (quotientStep h)
    mono_f := by
      change Mono (kernel.ι (quotientStep h))
      infer_instance
    epi_g := quotientStep_epi h }

/-- The normalized isomorphisms preserve the entire original short exact
kernel-line row, including both of its original maps. -/
def quotientKernelSequenceIso {S S' : Subobject Q} (h : S ≤ S') :
    quotientKernelSequence (comapSub_mono π h) ≅ quotientKernelSequence h :=
  ShortComplex.isoMk (quotientKernelIso π h) (quotientIso π S) (quotientIso π S')
    (quotientKernelIso_hom_ι π h) (quotientIso_step π h).symm

end M9Native.FlagQuotientLines

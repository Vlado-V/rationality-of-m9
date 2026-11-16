module

public import M9StacksIntegration.MukaiRankTwoPreimage

/-!
# The actual quotient of the rank-two preimage

For the original short exact sequence `η → E → G` and the actual line
sequence `L → G → N`, the original inclusion of `E ×_G L` into E is the
kernel of `E → G → N`. The resulting quotient sequence uses those exact
maps, with no new geometric, rank, or degree premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiRankTwoPreimage

universe u

namespace M9Native.MukaiRankTwoPreimageQuotient

variable {X : Scheme.{u}} (S : ShortComplex X.Modules)
    {L N : X.Modules} (j : L ⟶ S.X₃) (q : S.X₃ ⟶ N) (w : j ≫ q = 0)

include w

/-- The original inclusion is killed by the original quotient composite. -/
@[reassoc (attr := simp)]
theorem inclusion_comp_eq_zero : inclusion S j ≫ (S.g ≫ q) = 0 := by
  rw [← Category.assoc, inclusion_condition, Category.assoc, w, comp_zero]

/-- The literal sequence `E ×_G L → E → N`. -/
def quotientSequence : ShortComplex X.Modules :=
  ShortComplex.mk (inclusion S j) (S.g ≫ q) (inclusion_comp_eq_zero S j q w)

/-- The original pullback inclusion satisfies the actual universal
property of the kernel of the original quotient composite. -/
def inclusion_isKernel
    (hLine : (ShortComplex.mk j q w).ShortExact) :
    IsLimit (KernelFork.ofι (inclusion S j) (inclusion_comp_eq_zero S j q w)) := by
  let : Mono j := hLine.mono_f
  refine Fork.IsLimit.mk' _ fun s => ?_
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hLine.fIsKernel (s.ι ≫ S.g)
    (by simpa only [Category.assoc, comp_zero] using s.condition)
  simp only [KernelFork.ι_ofι] at hl
  refine ⟨pullback.lift s.ι l hl.symm, ?_, ?_⟩
  · simp [MukaiRankTwoPreimage.inclusion]
  · intro m hm
    simp only [KernelFork.ι_ofι, MukaiRankTwoPreimage.inclusion] at hm
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hm
    · rw [pullback.lift_snd]
      apply (cancel_mono j).mp
      calc
        (m ≫ pullback.snd S.g j) ≫ j = (m ≫ pullback.fst S.g j) ≫ S.g := by
          rw [Category.assoc, ← pullback.condition, ← Category.assoc]
        _ = s.ι ≫ S.g := by rw [show m ≫ pullback.fst S.g j = s.ι from hm]
        _ = l ≫ j := hl.symm

/-- Both original exact sequences prove that the literal preimage
inclusion has the actual quotient N. No separate preimage quotient
sequence is supplied. -/
theorem quotientSequence_shortExact (hS : S.ShortExact)
    (hLine : (ShortComplex.mk j q w).ShortExact) :
    (quotientSequence S j q w).ShortExact := by
  let : Epi S.g := hS.epi_g
  let : Epi q := hLine.epi_g
  obtain ⟨hex, hmono⟩ :=
    (quotientSequence S j q w).exact_and_mono_f_iff_f_is_kernel.mpr
      ⟨inclusion_isKernel S j q w hLine⟩
  refine { exact := hex, mono_f := hmono, epi_g := ?_ }
  change Epi (S.g ≫ q)
  infer_instance

end M9Native.MukaiRankTwoPreimageQuotient

module

public import M9StacksIntegration.FlagTowerLines
public import M9StacksIntegration.ShortExactKernelComparison

/-!
# Original native flag-cons kernel lines and actual tail quotients

The original native tower constructs its flag by the actual tautological
kernel inclusion. These comparisons retain its actual quotient maps and
identify the first resulting kernel line with the original tail quotient,
using the genuine cokernel-composite exact row. This attaches the named
flag lines to the actual projective-bundle tautological line mechanism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.FlagTower

universe u

namespace M9Native.FlagConsLines

variable {T : Scheme.{u}} {B M : T.Modules} (j : B ⟶ M) [Mono j]

local instance actualHasCokernels : HasCokernels T.Modules := inferInstance
local instance actualHasKernels : HasKernels T.Modules := inferInstance
local instance actualHasCokernel {A D : T.Modules} (f : A ⟶ D) : HasCokernel f :=
  HasCokernels.has_colimit f
local instance actualHasKernel {A D : T.Modules} (f : A ⟶ D) : HasKernel f :=
  HasKernels.has_limit f

/-- The kernel of the original cokernel projection of a mono is its subobject. -/
theorem kernel_cokernel_mono {A : T.Modules} (f : A ⟶ M) [Mono f] :
    kernelSubobject (cokernel.π f) = Subobject.mk f := by
  rw [← PullbackQuotientLines.subobjectCokernelIso_π f,
    kernelSubobject_comp_mono, FlagQuotientLines.kernel_cokernel_subobject]

/-- Equality of the actual quotient kernels includes the original map law. -/
theorem exists_mappedQuotientIso (S : Subobject B) :
    ∃ e : cokernel ((Subobject.map j).obj S).arrow ≅ cokernel (S.arrow ≫ j),
      cokernel.π ((Subobject.map j).obj S).arrow ≫ e.hom = cokernel.π (S.arrow ≫ j) := by
  apply FlagQuotientLines.exists_iso_of_kernel_eq
  rw [FlagQuotientLines.kernel_cokernel_subobject, kernel_cokernel_mono]
  exact Flag.map_obj_eq_mk j S

/-- Normalized quotient by the original mapped subobject. -/
def mappedQuotientIso (S : Subobject B) :
    cokernel ((Subobject.map j).obj S).arrow ≅ cokernel (S.arrow ≫ j) :=
  Classical.choose (exists_mappedQuotientIso j S)

@[reassoc]
theorem mappedQuotientIso_π (S : Subobject B) :
    cokernel.π ((Subobject.map j).obj S).arrow ≫ (mappedQuotientIso j S).hom =
      cokernel.π (S.arrow ≫ j) :=
  Classical.choose_spec (exists_mappedQuotientIso j S)

/-- The true exact cokernel-composite row supplies the actual kernel iso. -/
def cokernelCompKernelIso {A : T.Modules} (a : A ⟶ B) :
    cokernel a ≅ kernel (Stacks.Chow.GenuineChern.cokernelCompSequence a j).g := by
  let e := (Stacks.Chow.GenuineChern.shortExact_cokernelCompSequence a j).fIsKernel.conePointUniqueUpToIso
      (kernelIsKernel (Stacks.Chow.GenuineChern.cokernelCompSequence a j).g)
  exact e

@[reassoc]
theorem cokernelCompKernelIso_hom_ι {A : T.Modules} (a : A ⟶ B) :
    (cokernelCompKernelIso j a).hom ≫
      kernel.ι (Stacks.Chow.GenuineChern.cokernelCompSequence a j).g =
        (Stacks.Chow.GenuineChern.cokernelCompSequence a j).f :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (Stacks.Chow.GenuineChern.shortExact_cokernelCompSequence a j).fIsKernel
    (kernelIsKernel (Stacks.Chow.GenuineChern.cokernelCompSequence a j).g)
    WalkingParallelPair.zero

variable (hj : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel j) 1)
  {m : ℕ} (F : Flag B m)

/-- The first original quotient of native cons is the actual cokernel of j. -/
def firstQuotientIso :
    FlagTowerLines.quotient (Flag.cons j hj F) 0 ≅ cokernel j :=
  PullbackQuotientLines.subobjectCokernelIso j

@[reassoc]
theorem firstQuotientIso_π :
    cokernel.π ((Flag.cons j hj F).sub 0).arrow ≫ (firstQuotientIso j hj F).hom =
      cokernel.π j := PullbackQuotientLines.subobjectCokernelIso_π j

/-- The original successor quotient is the actual cokernel of the composite. -/
def succQuotientIso (i : Fin m) :
    FlagTowerLines.quotient (Flag.cons j hj F) i.succ ≅ cokernel ((F.sub i).arrow ≫ j) :=
  mappedQuotientIso j (F.sub i)

@[reassoc]
theorem succQuotientIso_π (i : Fin m) :
    cokernel.π ((Flag.cons j hj F).sub i.succ).arrow ≫ (succQuotientIso j hj F i).hom =
      cokernel.π ((F.sub i).arrow ≫ j) := mappedQuotientIso_π j (F.sub i)

/-- The original first quotient step is the literal cokernel-composite step. -/
theorem firstStep_square (i : Fin m) :
    FlagTowerLines.quotientStep (Flag.cons j hj F) (Fin.zero_le i.succ) ≫
        (firstQuotientIso j hj F).hom =
      (succQuotientIso j hj F i).hom ≫
        (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub i).arrow j).g := by
  let Q := Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub i).arrow j
  have hQ : cokernel.π ((F.sub i).arrow ≫ j) ≫ Q.g = cokernel.π j :=
    (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  apply (cancel_epi (cokernel.π ((Flag.cons j hj F).sub i.succ).arrow)).mp
  calc
    _ = (cokernel.π ((Flag.cons j hj F).sub i.succ).arrow ≫
        FlagTowerLines.quotientStep (Flag.cons j hj F) (Fin.zero_le i.succ)) ≫
          (firstQuotientIso j hj F).hom := (Category.assoc _ _ _).symm
    _ = cokernel.π ((Flag.cons j hj F).sub 0).arrow ≫ (firstQuotientIso j hj F).hom :=
      congrArg (fun f => f ≫ (firstQuotientIso j hj F).hom)
        (FlagQuotientLines.quotientStep_π ((Flag.cons j hj F).antitone (Fin.zero_le i.succ)))
    _ = cokernel.π j := firstQuotientIso_π j hj F
    _ = cokernel.π ((F.sub i).arrow ≫ j) ≫ Q.g := hQ.symm
    _ = (cokernel.π ((Flag.cons j hj F).sub i.succ).arrow ≫
        (succQuotientIso j hj F i).hom) ≫ Q.g :=
      congrArg (fun f => f ≫ Q.g) (succQuotientIso_π j hj F i).symm
    _ = _ := Category.assoc _ _ _

/-- The actual first kernel line in the extended flag is its actual tail quotient. -/
def firstKernelLineIso (i : Fin m) :
    FlagTowerLines.kernelLine (Flag.cons j hj F) (Fin.zero_le i.succ) ≅
      FlagTowerLines.quotient F i :=
  kernel.mapIso _ _ (succQuotientIso j hj F i) (firstQuotientIso j hj F)
    (firstStep_square j hj F i) ≪≫ (cokernelCompKernelIso j (F.sub i).arrow).symm

end M9Native.FlagConsLines

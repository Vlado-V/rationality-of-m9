module

public import M9StacksIntegration.FlagConsLines

/-!
# Successor kernel lines of the original native cons flag

The actual cokernel-composite rows share the same original final
quotient. Their original quotient maps force the commuting diagram;
the genuine two-row kernel comparison then identifies the actual
successor kernel lines with the original tail kernel lines.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.FlagTower

universe u

namespace M9Native.FlagConsSuccessorLines

variable {T : Scheme.{u}} {B M : T.Modules} (j : B ⟶ M) [Mono j]
  (hj : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel j) 1)
  {m : ℕ} (F : Flag B m) {a b : Fin m}

local instance actualHasCokernels : HasCokernels T.Modules := inferInstance
local instance actualHasKernels : HasKernels T.Modules := inferInstance
local instance actualHasCokernel {A D : T.Modules} (f : A ⟶ D) : HasCokernel f :=
  HasCokernels.has_colimit f
local instance actualHasKernel {A D : T.Modules} (f : A ⟶ D) : HasKernel f :=
  HasKernels.has_limit f

/-- The actual quotient step between cokernels of the original composite arrows. -/
def nativeStep (h : a ≤ b) :
    cokernel ((F.sub b).arrow ≫ j) ⟶ cokernel ((F.sub a).arrow ≫ j) :=
  cokernel.desc ((F.sub b).arrow ≫ j) (cokernel.π ((F.sub a).arrow ≫ j)) (by
    calc
      ((F.sub b).arrow ≫ j) ≫ cokernel.π ((F.sub a).arrow ≫ j) =
        Subobject.ofLE _ _ (F.antitone h) ≫
          (((F.sub a).arrow ≫ j) ≫ cokernel.π ((F.sub a).arrow ≫ j)) := by
            rw [← Subobject.ofLE_arrow (F.antitone h)]
            simp only [Category.assoc]
      _ = 0 := by rw [cokernel.condition, comp_zero])

@[reassoc]
theorem nativeStep_π (h : a ≤ b) :
    cokernel.π ((F.sub b).arrow ≫ j) ≫ nativeStep j F h =
      cokernel.π ((F.sub a).arrow ≫ j) := cokernel.π_desc _ _ _

/-- The left squares of the two actual cokernel-composite exact rows commute. -/
theorem nativeLeft_square (h : a ≤ b) :
    (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub b).arrow j).f ≫ nativeStep j F h =
      FlagTowerLines.quotientStep F h ≫
        (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub a).arrow j).f := by
  have hfb : cokernel.π (F.sub b).arrow ≫
      (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub b).arrow j).f =
        j ≫ cokernel.π ((F.sub b).arrow ≫ j) := cokernel.π_desc _ _ _
  have hfa : cokernel.π (F.sub a).arrow ≫
      (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub a).arrow j).f =
        j ≫ cokernel.π ((F.sub a).arrow ≫ j) := cokernel.π_desc _ _ _
  apply (cancel_epi (cokernel.π (F.sub b).arrow)).mp
  calc
    _ = (j ≫ cokernel.π ((F.sub b).arrow ≫ j)) ≫ nativeStep j F h := by
      rw [← Category.assoc, hfb]
    _ = j ≫ cokernel.π ((F.sub a).arrow ≫ j) := by rw [Category.assoc, nativeStep_π]
    _ = cokernel.π (F.sub a).arrow ≫
        (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub a).arrow j).f := hfa.symm
    _ = _ := by rw [← Category.assoc, FlagQuotientLines.quotientStep_π]

/-- The final vertical map is the identity on the original cokernel of j. -/
theorem nativeRight_square (h : a ≤ b) :
    nativeStep j F h ≫ (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub a).arrow j).g =
      (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub b).arrow j).g := by
  have hga : cokernel.π ((F.sub a).arrow ≫ j) ≫
      (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub a).arrow j).g =
        cokernel.π j := (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  have hgb : cokernel.π ((F.sub b).arrow ≫ j) ≫
      (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub b).arrow j).g =
        cokernel.π j := (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  apply (cancel_epi (cokernel.π ((F.sub b).arrow ≫ j))).mp
  calc
    _ = cokernel.π ((F.sub a).arrow ≫ j) ≫
        (Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub a).arrow j).g := by
      rw [← Category.assoc, nativeStep_π]
    _ = cokernel.π j := hga
    _ = _ := hgb.symm

/-- The native successor quotient step is this same actual composite-arrow step. -/
theorem successorStep_square (h : a ≤ b) :
    FlagTowerLines.quotientStep (Flag.cons j hj F) (show a.succ ≤ b.succ from Nat.succ_le_succ h) ≫
        (FlagConsLines.succQuotientIso j hj F a).hom =
      (FlagConsLines.succQuotientIso j hj F b).hom ≫ nativeStep j F h := by
  apply (cancel_epi (cokernel.π ((Flag.cons j hj F).sub b.succ).arrow)).mp
  calc
    _ = (cokernel.π ((Flag.cons j hj F).sub b.succ).arrow ≫
        FlagTowerLines.quotientStep (Flag.cons j hj F) (show a.succ ≤ b.succ from Nat.succ_le_succ h)) ≫
          (FlagConsLines.succQuotientIso j hj F a).hom := (Category.assoc _ _ _).symm
    _ = cokernel.π ((Flag.cons j hj F).sub a.succ).arrow ≫
        (FlagConsLines.succQuotientIso j hj F a).hom :=
      congrArg (fun f => f ≫ (FlagConsLines.succQuotientIso j hj F a).hom)
        (FlagQuotientLines.quotientStep_π ((Flag.cons j hj F).antitone (show a.succ ≤ b.succ from Nat.succ_le_succ h)))
    _ = cokernel.π ((F.sub a).arrow ≫ j) := FlagConsLines.succQuotientIso_π j hj F a
    _ = cokernel.π ((F.sub b).arrow ≫ j) ≫ nativeStep j F h := (nativeStep_π j F h).symm
    _ = (cokernel.π ((Flag.cons j hj F).sub b.succ).arrow ≫
        (FlagConsLines.succQuotientIso j hj F b).hom) ≫ nativeStep j F h :=
      congrArg (fun f => f ≫ nativeStep j F h) (FlagConsLines.succQuotientIso_π j hj F b).symm
    _ = _ := Category.assoc _ _ _

/-- The original actual successor kernel line is its original tail kernel line. -/
def successorKernelLineIso (h : a ≤ b) :
    FlagTowerLines.kernelLine (Flag.cons j hj F) (show a.succ ≤ b.succ from Nat.succ_le_succ h) ≅
      FlagTowerLines.kernelLine F h := by
  let Sb := Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub b).arrow j
  let Sa := Stacks.Chow.GenuineChern.cokernelCompSequence (F.sub a).arrow j
  let e := ShortExactKernelComparison.kernelIso Sb.f Sb.g Sb.zero
    (Stacks.Chow.GenuineChern.shortExact_cokernelCompSequence (F.sub b).arrow j)
    Sa.f Sa.g Sa.zero
    (Stacks.Chow.GenuineChern.shortExact_cokernelCompSequence (F.sub a).arrow j)
    (FlagTowerLines.quotientStep F h) (nativeStep j F h)
    (nativeLeft_square j F h) (nativeRight_square j F h)
  exact kernel.mapIso _ _ (FlagConsLines.succQuotientIso j hj F b)
    (FlagConsLines.succQuotientIso j hj F a) (successorStep_square j hj F h) ≪≫ e.symm

end M9Native.FlagConsSuccessorLines

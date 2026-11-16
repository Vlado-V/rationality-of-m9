module

public import M9StacksIntegration.FlagQuotientLines
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Normalized actual pullback quotients and their original step maps

All objects are actual modules on actual schemes. The cokernel
comparison is derived from the genuine pullback functor. The original
quotient maps normalize it and constrain the named quotient steps.
The final kernel here is the kernel of the mapped step; identifying
it with the pullback of the original kernel additionally requires
true kernel preservation and is kept as a separate geometric step.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.PullbackQuotientLines

section Underlying

variable {X : Scheme.{u}} {A M : X.Modules} (f : A ⟶ M) [Mono f]

/-- Replacing a mono by its actual subobject arrow retains its cokernel. -/
def subobjectCokernelIso : cokernel (Subobject.mk f).arrow ≅ cokernel f :=
  cokernel.mapIso (Subobject.mk f).arrow f (Subobject.underlyingIso f) (Iso.refl _)
    (by simp)

@[reassoc]
theorem subobjectCokernelIso_π :
    cokernel.π (Subobject.mk f).arrow ≫ (subobjectCokernelIso f).hom = cokernel.π f := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

end Underlying

section Pullback

variable {X Y : Scheme.{u}} (i : Y ⟶ X) {A M : X.Modules} (f : A ⟶ M)
  {N : Y.Modules} (e : N ≅ (Scheme.Modules.pullback i).obj M)

/-- The original pulled-back arrow, expressed in its actual source model. -/
abbrev changedArrow := (Scheme.Modules.pullback i).map f ≫ e.inv

/-- Actual cokernel comparison, including the original source isomorphism. -/
def cokernelIso :
    cokernel (changedArrow i f e) ≅ (Scheme.Modules.pullback i).obj (cokernel f) :=
  cokernelCompIsIso ((Scheme.Modules.pullback i).map f) e.inv ≪≫
    asIso (cokernelComparison f (Scheme.Modules.pullback i))

@[reassoc]
theorem cokernelIso_π :
    cokernel.π (changedArrow i f e) ≫ (cokernelIso i f e).hom =
      e.hom ≫ (Scheme.Modules.pullback i).map (cokernel.π f) := by
  simp [cokernelIso, changedArrow, cokernelCompIsIso_hom, Category.assoc]

/-- The original quotient-map normalization uniquely fixes the comparison. -/
theorem cokernelIso_unique
    (j : cokernel (changedArrow i f e) ≅ (Scheme.Modules.pullback i).obj (cokernel f))
    (hj : cokernel.π (changedArrow i f e) ≫ j.hom =
      e.hom ≫ (Scheme.Modules.pullback i).map (cokernel.π f)) :
    j = cokernelIso i f e := by
  apply Iso.ext
  exact (cancel_epi (cokernel.π (changedArrow i f e))).mp
    (hj.trans (cokernelIso_π i f e).symm)

end Pullback

section Subobjects

variable {X Y : Scheme.{u}} (i : Y ⟶ X) {M : X.Modules}
  {N : Y.Modules} (e : N ≅ (Scheme.Modules.pullback i).obj M)

/-- Literal subobject used when a genuine original subobject pulls back mono. -/
def subobjectPullback (S : Subobject M) [Mono ((Scheme.Modules.pullback i).map S.arrow)] :
    Subobject N :=
  Subobject.mk (changedArrow i S.arrow e)

/-- The actual quotient by the actual pulled-back subobject. -/
def quotientIso (S : Subobject M) [Mono ((Scheme.Modules.pullback i).map S.arrow)] :
    cokernel (subobjectPullback i e S).arrow ≅
      (Scheme.Modules.pullback i).obj (cokernel S.arrow) :=
  subobjectCokernelIso (changedArrow i S.arrow e) ≪≫ cokernelIso i S.arrow e

@[reassoc]
theorem quotientIso_π (S : Subobject M) [Mono ((Scheme.Modules.pullback i).map S.arrow)] :
    cokernel.π (subobjectPullback i e S).arrow ≫ (quotientIso i e S).hom =
      e.hom ≫ (Scheme.Modules.pullback i).map (cokernel.π S.arrow) := by
  calc
    cokernel.π (subobjectPullback i e S).arrow ≫ (quotientIso i e S).hom =
        (cokernel.π (subobjectPullback i e S).arrow ≫
          (subobjectCokernelIso (changedArrow i S.arrow e)).hom) ≫
            (cokernelIso i S.arrow e).hom := (Category.assoc _ _ _).symm
    _ = cokernel.π (changedArrow i S.arrow e) ≫ (cokernelIso i S.arrow e).hom :=
      congrArg (fun q => q ≫ (cokernelIso i S.arrow e).hom)
        (subobjectCokernelIso_π (changedArrow i S.arrow e))
    _ = _ := cokernelIso_π i S.arrow e

variable {S S' : Subobject M} [Mono ((Scheme.Modules.pullback i).map S.arrow)]
  [Mono ((Scheme.Modules.pullback i).map S'.arrow)]

/-- The pulled-back actual inclusions remain nested. -/
theorem subobjectPullback_le (h : S ≤ S') :
    subobjectPullback i e S ≤ subobjectPullback i e S' :=
  Subobject.mk_le_mk_of_comm ((Scheme.Modules.pullback i).map (Subobject.ofLE S S' h)) (by
    change (Scheme.Modules.pullback i).map (Subobject.ofLE S S' h) ≫
      ((Scheme.Modules.pullback i).map S'.arrow ≫ e.inv) =
      (Scheme.Modules.pullback i).map S.arrow ≫ e.inv
    rw [← Category.assoc, ← Functor.map_comp, Subobject.ofLE_arrow])

/-- The actual normalized quotient comparisons preserve the original step. -/
theorem quotientIso_step (h : S ≤ S') :
    FlagQuotientLines.quotientStep (subobjectPullback_le i e h) ≫ (quotientIso i e S').hom =
      (quotientIso i e S).hom ≫
        (Scheme.Modules.pullback i).map (FlagQuotientLines.quotientStep h) := by
  apply (cancel_epi (cokernel.π (subobjectPullback i e S).arrow)).mp
  simp only [FlagQuotientLines.quotientStep_π_assoc,
    quotientIso_π, quotientIso_π_assoc]
  rw [← Functor.map_comp, FlagQuotientLines.quotientStep_π]

/-- Actual kernel comparison induced by the constrained original quotient
square. Kernel preservation for the pullback functor is not assumed here. -/
def quotientKernelMapIso (h : S ≤ S') :
    kernel (FlagQuotientLines.quotientStep (subobjectPullback_le i e h)) ≅
      kernel ((Scheme.Modules.pullback i).map (FlagQuotientLines.quotientStep h)) :=
  kernel.mapIso _ _ (quotientIso i e S) (quotientIso i e S') (quotientIso_step i e h)

@[reassoc]
theorem quotientKernelMapIso_hom_ι (h : S ≤ S') :
    (quotientKernelMapIso i e h).hom ≫
        kernel.ι ((Scheme.Modules.pullback i).map (FlagQuotientLines.quotientStep h)) =
      kernel.ι (FlagQuotientLines.quotientStep (subobjectPullback_le i e h)) ≫
        (quotientIso i e S).hom :=
  kernel.lift_ι _ _ _

end Subobjects

end M9Native.PullbackQuotientLines

module

public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismPresentation
public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningBaseDescent
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAlgebraExtensionBridge

/-! Genuine restriction of an actual compatible thickening morphism to
another base, and simultaneous equality transport of its two extensions. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening

universe u

namespace M9Native.RawCompatibleMorphismOperations

variable {Y X S T : RingedSpace.{u,u}} {f : Y ⟶ S} {g : X ⟶ Y}
  {F : SheafOfModules.{u} (structureSheafRing Y)}
  {G : SheafOfModules.{u} (structureSheafRing X)}

def restricted (p : S ⟶ T) (P : SquareZeroAlgebraExtension f F) :
    SquareZeroAlgebraExtension (f ≫ p) F where
  toAlgebraSquareZeroExtension := P.toAlgebraSquareZeroExtension.restrictBase p
  ideal_bijective := P.ideal_bijective

def rebased {f' : Y ⟶ S} (e : f = f') (P : SquareZeroAlgebraExtension f F) :
    SquareZeroAlgebraExtension f' F := e ▸ P

/-- Restrict both actual extensions and their actual comorphism. -/
def restrictCompatible (p : S ⟶ T) {P : SquareZeroAlgebraExtension f F}
    {Q : SquareZeroAlgebraExtension (g ≫ f) G} {c : F ⟶ (modulePushforward g).obj G}
    (h : CompatibleMorphism P Q c) :
    CompatibleMorphism (restricted p P) (restricted p Q) c where
  hom := h.hom
  reduction_comm := h.reduction_comm
  base_comm := by
    have hP := adjointBaseHom_baseInverseImageRingMap_comp p f P.sheaf P.base
    have hQ := adjointBaseHom_baseInverseImageRingMap_comp p (g ≫ f) Q.sheaf Q.base
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    have hPU := congrArg (fun a => a.hom.app U) hP
    have hQU := congrArg (fun a => a.hom.app U) hQ
    have hb := congrArg (fun a => a.hom.app ((Opens.map p.hom.base).op.obj U)) h.base_comm
    change P.toAlgebraSquareZeroExtension.adjointBase.hom.app
        ((Opens.map p.hom.base).op.obj U) ≫
        h.hom.hom.app ((Opens.map (f ≫ p).hom.base).op.obj U) =
      Q.toAlgebraSquareZeroExtension.adjointBase.hom.app
        ((Opens.map p.hom.base).op.obj U) at hb
    change (restricted p P).toAlgebraSquareZeroExtension.adjointBase.hom.app U ≫
        h.hom.hom.app ((Opens.map (f ≫ p).hom.base).op.obj U) =
      (restricted p Q).toAlgebraSquareZeroExtension.adjointBase.hom.app U
    refine (congrArg (fun a => a ≫
      h.hom.hom.app ((Opens.map (f ≫ p).hom.base).op.obj U)) hPU).trans ?_
    refine Eq.trans ?_ hQU.symm
    have hh := congrArg (fun a => p.hom.c.app U ≫ a) hb
    change (p.hom.c.app U ≫ P.toAlgebraSquareZeroExtension.adjointBase.hom.app
        ((Opens.map p.hom.base).op.obj U)) ≫
        h.hom.hom.app ((Opens.map (f ≫ p).hom.base).op.obj U) =
      p.hom.c.app U ≫ Q.toAlgebraSquareZeroExtension.adjointBase.hom.app
        ((Opens.map p.hom.base).op.obj U)
    simpa only [Category.assoc] using hh

  ideal_comm := h.ideal_comm

/-- Rebase both objects together. The original comorphism and ideal map
are transported as actual data, without any class equality premise. -/
def rebaseCompatible {f' : Y ⟶ S} (e : f = f')
    {P : SquareZeroAlgebraExtension f F} {Q : SquareZeroAlgebraExtension (g ≫ f) G}
    {c : F ⟶ (modulePushforward g).obj G} (h : CompatibleMorphism P Q c) :
    CompatibleMorphism (rebased e P) (rebased (congrArg (fun q => g ≫ q) e) Q) c := by
  subst f'
  exact h

end M9Native.RawCompatibleMorphismOperations

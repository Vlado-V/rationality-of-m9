module

public import M9StacksIntegration.SectionZeroEvaluation
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic

/-! Evaluation at a finite locally free section presents the structure
module of its native zero scheme. The image is the actual native ideal,
including nilpotents, and epimorphy onto that ideal is proved locally. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.SectionZeroCokernel

variable {X : Scheme.{u}}

abbrev structureModule (I : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)

abbrev quotientMap (I : X.IdealSheafData) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ structureModule I :=
  Stacks.IdealSheafSequence.divisorQuotientMap I

instance quotientMap_epi (I : X.IdealSheafData) : Epi (quotientMap I) :=
  Stacks.IdealSheafSequence.epi_divisorQuotientMap I

abbrev idealMap (I : X.IdealSheafData) :
    idealSheafModule I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  Stacks.IdealSheafSequence.divisorIdealMap I

theorem idealMap_condition (I : X.IdealSheafData) : idealMap I ≫ quotientMap I = 0 :=
  kernel.condition (Stacks.IdealSheafSequence.divisorQuotientMap I)

def idealMap_isKernel (I : X.IdealSheafData) :
    IsLimit (KernelFork.ofι (idealMap I) (idealMap_condition I)) :=
  kernelIsKernel (Stacks.IdealSheafSequence.divisorQuotientMap I)

def quotientMap_isCokernel (I : X.IdealSheafData) :
    IsColimit (CokernelCofork.ofπ (quotientMap I) (idealMap_condition I)) := by
  let : Epi (quotientMap I) := quotientMap_epi I
  exact Abelian.epiIsCokernelOfKernel (C := X.Modules) (f := quotientMap I)
    (KernelFork.ofι (idealMap I) (idealMap_condition I)) (idealMap_isKernel I)

def idealCokernelIso (I : X.IdealSheafData) : cokernel (idealMap I) ≅ structureModule I :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (C := X.Modules) (idealMap I))
    (quotientMap_isCokernel I)

@[reassoc]
theorem idealCokernelIso_projection (I : X.IdealSheafData) :
    cokernel.π (idealMap I) ≫ (idealCokernelIso I).hom = quotientMap I :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (C := X.Modules) (idealMap I))
    (quotientMap_isCokernel I) WalkingParallelPair.one

variable (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E] (s : Γ(E,⊤))

theorem evaluation_factor :
    SectionZeroEvaluation.evaluationIdealMap E s ≫
      idealMap (Stacks.Chow.zeroSchemeOfSection X E s) = dualEvalHom E s := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun t => ?_))
  exact SectionZeroEvaluation.evaluationIdealMap_eval E s U.unop t

/-- The actual cokernel of dual evaluation is the pushforward of the
structure module of the actual native section-zero scheme. -/
def evaluationCokernelIso :
    cokernel (dualEvalHom E s) ≅ structureModule (Stacks.Chow.zeroSchemeOfSection X E s) := by
  let : Epi (SectionZeroEvaluation.evaluationIdealMap E s) :=
    SectionZeroEvaluation.evaluationIdealMap_epi E s
  exact cokernelIsoOfEq (evaluation_factor E s).symm ≪≫
    cokernelEpiComp (SectionZeroEvaluation.evaluationIdealMap E s)
      (idealMap (Stacks.Chow.zeroSchemeOfSection X E s)) ≪≫
        idealCokernelIso (Stacks.Chow.zeroSchemeOfSection X E s)

@[reassoc]
theorem evaluationCokernelIso_projection :
    cokernel.π (dualEvalHom E s) ≫ (evaluationCokernelIso E s).hom =
      quotientMap (Stacks.Chow.zeroSchemeOfSection X E s) := by
  dsimp only [evaluationCokernelIso]
  rw [Iso.trans_hom,Iso.trans_hom,π_comp_cokernelIsoOfEq_hom_assoc,
    cokernelEpiComp_hom,cokernel.π_desc_assoc,idealCokernelIso_projection]

end M9Native.SectionZeroCokernel
end

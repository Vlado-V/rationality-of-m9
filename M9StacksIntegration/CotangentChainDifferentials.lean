module

public import M9StacksIntegration.CotangentCokernelDifferentials

/-!
# Original differential coordinates for an actual cotangent chain map

This arbitrary-site construction keeps each original coefficient category
fixed. It accepts an actual chain map, constructs its cokernel map and
computes its differential values from the original variable generators.
The ringed-space direct presentation supplies that generator calculation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite universalDerivationOfSite)

universe u

namespace M9Native.CotangentChainDifferentials

variable {C C₀ : Type u} [Category.{u} C] [Category.{u} C₀]
  (J : GrothendieckTopology C) (J₀ : GrothendieckTopology C₀)
  [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J₀ CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : C₀ ⥤ C) [F.IsContinuous J₀ J]
  (A B : Sheaf J CommRingCat.{u}) (a : A ⟶ B)
  (A₀ B₀ : Sheaf J₀ CommRingCat.{u}) (a₀ : A₀ ⟶ B₀)
  (φ : Stacks.SheafOfModules.Tensor.ringSheaf B₀ ⟶
    (F.sheafPushforwardContinuous RingCat.{u} J₀ J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf B))

abbrev pushforward :=
  _root_.SheafOfModules.pushforward.{u} φ

variable (α : naiveCotangentComplex.{u,u,u,u} J₀ A₀ B₀ a₀ ⟶
  ((pushforward J J₀ F B B₀ φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (naiveCotangentComplex.{u,u,u,u} J A B a))

/-- The genuine cokernel morphism of the given original chain map. -/
def cokernelMap :=
  CotangentCokernelMap.cokernelMap (pushforward J J₀ F B B₀ φ)
    (naiveCotangentComplex.{u,u,u,u} J₀ A₀ B₀ a₀)
    (naiveCotangentComplex.{u,u,u,u} J A B a) α

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Its actual projection square. -/
theorem π_comp_cokernelMap :
    cokernel.π ((naiveCotangentComplex.{u,u,u,u} J₀ A₀ B₀ a₀).d (-1) 0) ≫
      cokernelMap J J₀ F A B a A₀ B₀ a₀ φ α =
    α.f 0 ≫ (pushforward J J₀ F B B₀ φ).map
      (cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0)) :=
  CotangentCokernelMap.π_comp_cokernelMap _ _ _ _

/-- Read the actual cokernel map in original differential coordinates. -/
def differentialMap : moduleOfDifferentialsOfSite.{u,u,u,u} A₀ B₀ a₀ ⟶
    (pushforward J J₀ F B B₀ φ).obj (moduleOfDifferentialsOfSite.{u,u,u,u} A B a) :=
  (naiveCotangentCokernelIso.{u,u,u,u} J₀ A₀ B₀ a₀).inv ≫
    cokernelMap J J₀ F A B a A₀ B₀ a₀ φ α ≫
      (pushforward J J₀ F B B₀ φ).map (naiveCotangentCokernelIso.{u,u,u,u} J A B a).hom

/-- The constructed differential coordinates give the actual original
projection square, including the original cokernel isomorphisms. -/
theorem projection_square :
    cokernel.π ((naiveCotangentComplex.{u,u,u,u} J₀ A₀ B₀ a₀).d (-1) 0) ≫
      (naiveCotangentCokernelIso.{u,u,u,u} J₀ A₀ B₀ a₀).hom ≫
        differentialMap J J₀ F A B a A₀ B₀ a₀ φ α =
    α.f 0 ≫ (pushforward J J₀ F B B₀ φ).map
      (cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0) ≫
        (naiveCotangentCokernelIso.{u,u,u,u} J A B a).hom) := by
  simp only [differentialMap, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, π_comp_cokernelMap, Category.assoc, ← Functor.map_comp]

/-- Original variable-generator covariance computes the actual
universal differential, through the constructed cokernel square. -/
theorem differentialMap_d (U : C₀ᵒᵖ) (b : B₀.obj.obj U)
    (bT : B.obj.obj (F.op.obj U))
    (hvar : (α.f 0).val.app U (naiveCotangentVariableDifferential.{u,u,u,u} J₀ A₀ B₀ a₀ U b) =
      naiveCotangentVariableDifferential.{u,u,u,u} J A B a (F.op.obj U) bT) :
    (differentialMap J J₀ F A B a A₀ B₀ a₀ φ α).val.app U
      ((universalDerivationOfSite.{u,u,u,u} A₀ B₀ a₀).d b) =
      (universalDerivationOfSite.{u,u,u,u} A B a).d bT := by
  let eT := naiveCotangentCokernelIso.{u,u,u,u} J A B a
  have hπ := congrArg
    (fun m => m.val.app U (naiveCotangentVariableDifferential.{u,u,u,u} J₀ A₀ B₀ a₀ U b))
    (π_comp_cokernelMap J J₀ F A B a A₀ B₀ a₀ φ α)
  have hsrc := naiveCotangentCokernelDerivation_d.{u,u,u,u} J₀ A₀ B₀ a₀ U b
  have htgt := naiveCotangentCokernelDerivation_d.{u,u,u,u} J A B a (F.op.obj U) bT
  have he := congrArg (fun D => D.d bT)
    (CotangentCokernelDifferentials.cokernelDerivation_postcomp_differentialsIso J A B a)
  change eT.hom.val.app (F.op.obj U)
    ((cokernelMap J J₀ F A B a A₀ B₀ a₀ φ α).val.app U
      ((naiveCotangentCokernelDerivation.{u,u,u,u} J₀ A₀ B₀ a₀).d b)) = _
  calc
    _ = eT.hom.val.app (F.op.obj U)
        ((cokernelMap J J₀ F A B a A₀ B₀ a₀ φ α).val.app U
          ((cokernel.π ((naiveCotangentComplex.{u,u,u,u} J₀ A₀ B₀ a₀).d (-1) 0)).val.app U
            (naiveCotangentVariableDifferential.{u,u,u,u} J₀ A₀ B₀ a₀ U b))) :=
      congrArg (fun t => eT.hom.val.app (F.op.obj U)
        ((cokernelMap J J₀ F A B a A₀ B₀ a₀ φ α).val.app U t)) hsrc
    _ = eT.hom.val.app (F.op.obj U)
        ((cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0)).val.app (F.op.obj U)
          ((α.f 0).val.app U
            (naiveCotangentVariableDifferential.{u,u,u,u} J₀ A₀ B₀ a₀ U b))) :=
      congrArg (fun t => eT.hom.val.app (F.op.obj U) t) hπ
    _ = eT.hom.val.app (F.op.obj U)
        ((cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0)).val.app (F.op.obj U)
          (naiveCotangentVariableDifferential.{u,u,u,u} J A B a (F.op.obj U) bT)) :=
      congrArg (fun t => eT.hom.val.app (F.op.obj U)
        ((cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0)).val.app (F.op.obj U) t)) hvar
    _ = _ := (congrArg (fun t => eT.hom.val.app (F.op.obj U) t) htgt).symm.trans he

end M9Native.CotangentChainDifferentials

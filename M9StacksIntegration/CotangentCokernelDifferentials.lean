module

public import M9StacksIntegration.CotangentCokernelMap
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCokernelDerivation

/-!
# Original cotangent square maps on universal differentials

The cokernel map is constructed from the original native chain map of
an actual square. Its projection square follows from chain commutation.
Transport through the original cokernel/differentials isomorphisms then
restricts the original universal derivation along that square. No
cokernel commutation, derivation covariance, or H0 differential formula
is supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite universalDerivationOfSite)

universe u

namespace M9Native.CotangentCokernelDifferentials

open Stacks.SheafOfModules

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
  (ψ : A₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J₀ J).obj A)
  (β : B₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J₀ J).obj B)
  (hsq : a₀ ≫ β = ψ ≫ (F.sheafPushforwardContinuous CommRingCat.{u} J₀ J).map a)

/-- The actual coefficient pushforward of the original square. -/
abbrev squarePushforward :=
  _root_.SheafOfModules.pushforward.{u}
    (pushforwardRingHomOfSquare J₀ J F B B₀ β)

/-- The actual native cotangent chain map, retaining the original square. -/
abbrev squareChainMap :=
  naiveCotangentComplexPushforwardSquareMap.{u,u,u,u,u,u}
    J₀ J F A B a A₀ B₀ a₀ ψ β hsq

/-- The actual induced cokernel map, constructed rather than postulated. -/
def squareCokernelMap :=
  CotangentCokernelMap.cokernelMap (squarePushforward J J₀ F B B₀ β)
    (naiveCotangentComplex.{u,u,u,u} J₀ A₀ B₀ a₀)
    (naiveCotangentComplex.{u,u,u,u} J A B a)
    (squareChainMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Its projection compatibility is derived from the actual chain map. -/
theorem π_comp_squareCokernelMap :
    cokernel.π ((naiveCotangentComplex.{u,u,u,u} J₀ A₀ B₀ a₀).d (-1) 0) ≫
        squareCokernelMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq =
      (squareChainMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq).f 0 ≫
        (squarePushforward J J₀ F B B₀ β).map
          (cokernel.π ((naiveCotangentComplex.{u,u,u,u} J A B a).d (-1) 0)) :=
  CotangentCokernelMap.π_comp_cokernelMap _ _ _ _

/-- The actual original cokernel map read in the original differential sheaves. -/
def differentialMap : moduleOfDifferentialsOfSite.{u,u,u,u} A₀ B₀ a₀ ⟶
    (squarePushforward J J₀ F B B₀ β).obj
      (moduleOfDifferentialsOfSite.{u,u,u,u} A B a) :=
  (naiveCotangentCokernelIso.{u,u,u,u} J₀ A₀ B₀ a₀).inv ≫
    squareCokernelMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq ≫
    (squarePushforward J J₀ F B B₀ β).map
      (naiveCotangentCokernelIso.{u,u,u,u} J A B a).hom

/-- The actual universal derivation transported to the cokernel and back
is literally the original universal derivation. -/
theorem cokernelDerivation_postcomp_differentialsIso :
    (naiveCotangentCokernelDerivation.{u,u,u,u} J A B a).postcomp
        (naiveCotangentCokernelIso.{u,u,u,u} J A B a).hom.val =
      universalDerivationOfSite.{u,u,u,u} A B a := by
  ext U b
  exact congrArg
    (fun m : moduleOfDifferentialsOfSite.{u,u,u,u} A B a ⟶
      moduleOfDifferentialsOfSite.{u,u,u,u} A B a =>
        m.val.app U ((universalDerivationOfSite.{u,u,u,u} A B a).d b))
    (naiveCotangentCokernelIso.{u,u,u,u} J A B a).inv_hom_id

/-- The actual induced differential map restricts universal derivations
along the original square, with no supplied covariance equation. -/
theorem universalDerivation_postcomp_differentialMap :
    (universalDerivationOfSite.{u,u,u,u} A₀ B₀ a₀).postcomp
        (differentialMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq).val =
      derivationPushforwardOfSquare.{u,u,u,u,u,u}
        J A B a J₀ F A₀ B₀ a₀ ψ β hsq
        (universalDerivationOfSite.{u,u,u,u} A B a) := by
  have h := naiveCotangentCokernelDerivation_postcomp_pushforward.{u,u,u,u,u,u}
    J A B a J₀ F A₀ B₀ a₀ ψ β hsq
    (squareCokernelMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq)
    (π_comp_squareCokernelMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq)
    (naiveCotangentCokernelIso.{u,u,u,u} J A B a).hom
  rw [cokernelDerivation_postcomp_differentialsIso] at h
  exact h

/-- In particular the actual map sends d(b) to d(beta(b)) on every
original open, rather than only up to an unspecified automorphism. -/
theorem differentialMap_d (U : C₀ᵒᵖ) (b : B₀.obj.obj U) :
    (differentialMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq).val.app U
        ((universalDerivationOfSite.{u,u,u,u} A₀ B₀ a₀).d b) =
      (universalDerivationOfSite.{u,u,u,u} A B a).d
        ((β.hom.app U).hom b) :=
  congrArg (fun D => D.d b)
    (universalDerivation_postcomp_differentialMap J J₀ F A B a A₀ B₀ a₀ ψ β hsq)

end M9Native.CotangentCokernelDifferentials

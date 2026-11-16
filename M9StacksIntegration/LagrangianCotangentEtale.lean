module

public import M9StacksIntegration.LagrangianCotangentPullbackMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale

/-! Actual cotangent-map invertibility transported through the canonical étale differential. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianCotangentEtale

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianCotangentMap LagrangianCotangentPullbackNaturality LagrangianCotangentPullbackMap
open LagrangianIsotropicRestriction LagrangianSymmetricPullback
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X Y S : Scheme.{u}} {Q : Y.Modules}

/-- Genuine local invertibility of the pulled quotient's intrinsic map
implies invertibility of the original map's actual étale pullback. -/
theorem pullback_cotangentMap_isIso (g : X ⟶ Y) [Etale g] (p : Y ⟶ S)
    (q : freeOn Y 6 ⟶ Q) (hq : AnnihilatesSigma Y q)
    (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q)
    (hC : IsIso (cotangentMap (g ≫ p) (pulledQuotient g q)
      (pulledQuotient_annihilates g q hq))) :
    IsIso ((Scheme.Modules.pullback g).map (cotangentMap p q hq)) := by
  letI : IsIso (Stacks.Chow.pullbackDualMap g Q) := Stacks.Chow.pullbackDualMap_isIso g Q hQ
  letI : IsIso (symmetricMap (Stacks.Chow.pullbackDualMap g Q) 2) :=
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X
      ((Scheme.Modules.pullback g).obj (dualSheaf Q))).isIso_pieceMap
      (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X
        (dualSheaf ((Scheme.Modules.pullback g).obj Q)))
      (Stacks.Chow.pullbackDualMap g Q) inferInstance 2
  letI := hC
  letI : IsIso (pulledCotangentMap g p q hq) := by
    dsimp [pulledCotangentMap]
    infer_instance
  letI : IsIso (differentialMap g p) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_etale g p (g ≫ p) (𝟙 S)
      (Category.comp_id (g ≫ p)).symm
  letI : IsIso ((Scheme.Modules.pullback g).map (cotangentMap p q hq) ≫ differentialMap g p) :=
    (cotangentMap_pullback g p q hq).symm ▸ inferInstance
  exact (isIso_comp_right_iff ((Scheme.Modules.pullback g).map (cotangentMap p q hq))
    (differentialMap g p)).mp inferInstance

end M9Native.LagrangianCotangentEtale

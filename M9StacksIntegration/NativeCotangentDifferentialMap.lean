module

public import M9StacksIntegration.NativeCotangentPushCoordinates
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap

/-!
# The direct cotangent chain map gives the literal scheme differential

The adjoint of the constructed cokernel map is identified by its proved
local universal-derivation formula. Thus this uses the actual canonical
presentation chain map, with no differential compatibility assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.NativeCotangentDifferentialMap

variable {X Y S : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S)

/-- The actual direct-map cokernel morphism, transposed along the
original scheme pullback/pushforward adjunction. -/
def directMap :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
    (Scheme.Hom.relativeDifferentials f) (Scheme.Hom.relativeDifferentials (g ≫ f))).symm
    (NativeCotangentPushCoordinates.differentialsMap
      g.toLRSHom.toShHom f.toLRSHom.toShHom)

/-- The original direct canonical-presentation map has the actual local
differential formula on every original scheme open. -/
theorem directMap_app_d (U : Y.Opens) (b : Γ(Y,U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (directMap g f)).val.app (.op U)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) =
      (Scheme.Hom.universalRelativeDerivation (g ≫ f)).d ((g.app U).hom b) := by
  dsimp only [directMap]
  rw [Equiv.apply_symm_apply]
  exact NativeCotangentPushCoordinates.differentialsMap_d
    g.toLRSHom.toShHom f.toLRSHom.toShHom (.op U) b

/-- Hence the actual direct-map differential is the literal native
differential map, by the genuine universal property. -/
theorem directMap_eq :
    directMap g f = Scheme.Hom.relativeDifferentialsMap g f (g ≫ f) (𝟙 S) (by simp) := by
  apply (Scheme.Hom.isRelativeDifferentialsMap_iff_eq g f (g ≫ f) (𝟙 S) (by simp) _).mp
  exact directMap_app_d g f

end M9Native.NativeCotangentDifferentialMap

module

public import M9StacksIntegration.LagrangianCotangentActionQuotient
public import M9StacksIntegration.LagrangianPluckerEpimorphism

/-! Actual determinant-line transport under the native symplectic LG
action, retaining the original quotient and determinant sections. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianDeterminantAction

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient LagrangianPullback
open LagrangianCotangentActionQuotient LagrangianSymplecticAction LagrangianPluckerEpimorphism
open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K]
  {T : Scheme.{u}} (f : T ⟶ space K) (g : Matrix.symplecticGroup (Fin 3) K)

/-- The original acted quotient is compared with the original pulled
quotient, using its actual representing class. -/
def quotientActionIso : (pullbackPresentation (f ≫ action K g) (quotientOnLG K)).target ≅
    (pullbackPresentation f (quotientOnLG K)).target :=
  Classical.choose (pulled_action_isomorphic K f g)

theorem quotientActionIso_triangle :
    (pullbackPresentation (f ≫ action K g) (quotientOnLG K)).map ≫
        (quotientActionIso K f g).hom =
      (constantFreeIso K (f ≫ projection K) g).hom ≫
        (pullbackPresentation f (quotientOnLG K)).map :=
  Classical.choose_spec (pulled_action_isomorphic K f g)

/-- The actual determinant action is induced from the actual third
exterior power of the actual quotient comparison. -/
def determinantActionIso :
    (Scheme.Modules.pullback (f ≫ action K g)).obj (determinantLine K) ≅
      (Scheme.Modules.pullback f).obj (determinantLine K) :=
  determinantTransportIso K (f ≫ action K g) (quotientActionIso K f g) ≪≫
    (exteriorPullbackIso f (quotientOnLG K).target 3).symm

theorem coefficientMap_action :
    LagrangianPlucker.coefficientMap K (f ≫ action K g) =
      LagrangianPlucker.coefficientMap K f := by
  unfold LagrangianPlucker.coefficientMap
  rw [Category.assoc,action_projection]

/-- The determinant action retains every original primitive section as
the literal primitive determinant section of the precomposed quotient. -/
theorem determinantActionIso_primitive (j : Fin 14) :
    (determinantActionIso K f g).hom.app ⊤
      (pullbackGlobalSections (f ≫ action K g) (determinantLine K) (primitiveSections K j)) =
    (exteriorPullbackIso f (quotientOnLG K).target 3).inv.app ⊤
      (primitiveSection T K (LagrangianPlucker.coefficientMap K f)
        ((constantFreeIso K (f ≫ projection K) g).hom ≫
          (pullbackPresentation f (quotientOnLG K)).map) j) := by
  change (exteriorPullbackIso f (quotientOnLG K).target 3).inv.app ⊤
      ((determinantTransportIso K (f ≫ action K g) (quotientActionIso K f g)).hom.app ⊤
        (pullbackGlobalSections (f ≫ action K g) (determinantLine K) (primitiveSections K j))) = _
  rw [determinantTransportIso_primitive,quotientActionIso_triangle,coefficientMap_action]

end M9Native.LagrangianDeterminantAction

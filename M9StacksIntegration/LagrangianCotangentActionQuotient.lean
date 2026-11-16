module

public import M9StacksIntegration.LagrangianPluckerTrivialization
public import M9StacksIntegration.LagrangianSymplecticAction

/-! Actual universal quotient frames for translated native LG charts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianCotangentActionQuotient

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianPluckerTrivialization LagrangianSymplecticAction
open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K]

/-- The actual acted universal quotient is isomorphic to constant
ambient precomposition of the original actual pulled universal quotient,
with the original quotient map retained. -/
theorem pulled_action_isomorphic {T : Scheme.{u}} (f : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    ∃ e : (pullbackPresentation (f ≫ action K g) (quotientOnLG K)).target ≅
        (pullbackPresentation f (quotientOnLG K)).target,
      (pullbackPresentation (f ≫ action K g) (quotientOnLG K)).map ≫ e.hom=
        (constantFreeIso K (f ≫ projection K) g).hom ≫
          (pullbackPresentation f (quotientOnLG K)).map := by
  obtain ⟨eₐ,hₐ⟩ := pullbackPresentation_comp_isomorphic (inclusion K)
    (f ≫ action K g) (universalQuotient K)
  obtain ⟨e₀,h₀⟩ := pullbackPresentation_comp_isomorphic (inclusion K) f (universalQuotient K)
  obtain ⟨e₁,h₁⟩ := pullback_action_isomorphic K f g
  refine ⟨eₐ ≪≫ e₁ ≪≫ e₀.symm,?_⟩
  simp only [Iso.trans_hom,Iso.symm_hom,← Category.assoc]
  rw [hₐ,h₁]
  change ((constantFreeIso K (f ≫ projection K) g).hom ≫
    (pullbackPresentation (f ≫ inclusion K) (universalQuotient K)).map) ≫ e₀.inv=_
  simp only [← h₀,Category.assoc,e₀.hom_inv_id,Category.comp_id]

end M9Native.LagrangianCotangentActionQuotient

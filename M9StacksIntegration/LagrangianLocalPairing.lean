module

public import M9StacksIntegration.LagrangianLocalIsotropy
public import M9StacksIntegration.LagrangianIsotropicRestriction
public import M9StacksIntegration.LagrangianSymmetricLiftNaturality

/-! The actual intrinsic symmetric cotangent pairing on every open. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianLocalPairing

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianIsotropicDual LagrangianIsotropicRestriction LagrangianLocalIsotropy
open LagrangianCotangentFormula
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X S : Scheme.{u}} {Q : X.Modules}

/-- Actual exterior-isotropy implies isotropy of the original dual
coefficient functions on every open, with no trivialization hypothesis. -/
theorem coefficientMap_isotropic (q : freeOn X 6 ⟶ Q) (hq : AnnihilatesSigma X q)
    (U : X.Opens) (α β : Γ(dualSheaf Q,U)) :
    symplecticPair (coefficientMap q U α) (coefficientMap q U β)=0 := by
  let qU := restrictedQuotient q U
  let αU := functionalSection (Q.restrict U.ι) (localFunctional Q U α)
  let βU := functionalSection (Q.restrict U.ι) (localFunctional Q U β)
  have hc (γ : Γ(dualSheaf Q,U)) (j : Fin 6) :
      (Scheme.Opens.topIso U).hom
        (coefficientMap qU ⊤
          (functionalSection (Q.restrict U.ι) (localFunctional Q U γ)) j)=
        coefficientMap q U γ j := by
    simp only [coefficientMap_apply,quotientVector,evalAt_functionalSection]
    simp only [show homOfLE (show (⊤ : (U : Scheme.{u}).Opens)≤⊤ from le_top)=𝟙 ⊤
      from Subsingleton.elim _ _,op_id]
    rw [(Q.restrict U.ι).presheaf.map_id]
    change (Scheme.Opens.topIso U).hom ((localFunctional Q U γ).app ⊤
      (qU.app ⊤ (freeVector (U : Scheme.{u}) j)))=_
    rw [localFunctional_top_evaluation,restrictedQuotient_basis]
    rfl
  have h := congrArg (fun r => (Scheme.Opens.topIso U).hom r)
    (coefficientMap_top_isotropic qU (restrictedQuotient_annihilates q hq U) αU βU)
  simpa only [αU,βU,symplecticPair,map_sum,map_sub,map_mul,map_zero,hc] using h

/-- The canonical symmetric bilinear form valued in the actual relative
cotangent sheaf, defined through the actual universal derivation. -/
def localPairing (p : X ⟶ S) (q : freeOn X 6 ⟶ Q) (hq : AnnihilatesSigma X q)
    (U : X.Opens) :
    Γ(dualSheaf Q,U) →ₗ[Γ(X,U)] Γ(dualSheaf Q,U) →ₗ[Γ(X,U)]
      Γ(Scheme.Hom.relativeDifferentials p,U) :=
  intrinsicBilinear (localDerivation p U) (coefficientMap q U)
    (coefficientMap_isotropic q hq U)

theorem localPairing_symmetric (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (U : X.Opens) (α β : Γ(dualSheaf Q,U)) :
    localPairing p q hq U α β=localPairing p q hq U β α :=
  intrinsicBilinear_symmetric _ _ _ α β

/-- The intrinsic pairing commutes with every actual restriction. -/
theorem localPairing_map (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) {U V : X.Opens} (h : V≤U)
    (α β : Γ(dualSheaf Q,U)) :
    (Scheme.Hom.relativeDifferentials p).presheaf.map (homOfLE h).op
      (localPairing p q hq U α β)=
      localPairing p q hq V
        ((dualSheaf Q).presheaf.map (homOfLE h).op α)
        ((dualSheaf Q).presheaf.map (homOfLE h).op β) := by
  change (Scheme.Hom.relativeDifferentials p).presheaf.map (homOfLE h).op
      (differentialPair (localDerivation p U) (coefficientMap q U) α β)=
    differentialPair (localDerivation p V) (coefficientMap q V) _ _
  simp only [differentialPair,map_sum,map_sub,Scheme.Modules.map_smul,
    coefficientMap_map,localDerivation_map]

end M9Native.LagrangianLocalPairing

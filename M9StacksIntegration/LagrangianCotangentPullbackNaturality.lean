module

public import M9StacksIntegration.LagrangianPullbackCoefficientUnits
public import M9StacksIntegration.LagrangianSymmetricPullbackProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap

/-! The original intrinsic cotangent formula under genuine scheme pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators TensorProduct

universe u

namespace M9Native.LagrangianCotangentPullbackNaturality

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianCotangentMap LagrangianCotangentFormula LagrangianLocalPairing
open LagrangianIsotropicRestriction LagrangianPullbackCoefficientUnits
open LagrangianSymmetricPullbackProduct LagrangianSymmetricLiftNaturality
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X Y S : Scheme.{u}} {Q : Y.Modules}

/-- The actual adjunction unit, with its genuine scalar semilinearity. -/
def pullbackSections (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens) :
    Γ(F,U) →ₛₗ[(g.app U).hom] Γ((Scheme.Modules.pullback g).obj F,g ⁻¹ᵁ U) where
  toFun := pullbackUnit g F U
  map_add' x y := (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).val.app
    (op U)).hom.map_add x y
  map_smul' r x := (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).val.app
    (op U)).hom.map_smul r x

/-- The literal canonical map on native relative differentials. -/
def differentialMap (g : X ⟶ Y) (p : Y ⟶ S) :
    (Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials p) ⟶
      Scheme.Hom.relativeDifferentials (g ≫ p) :=
  Scheme.Hom.relativeDifferentialsMap g p (g ≫ p) (𝟙 S) (Category.comp_id (g ≫ p)).symm

/-- The actual differential map acts semilinearly on original local
sections through the genuine pullback unit. -/
def differentialSections (g : X ⟶ Y) (p : Y ⟶ S) (U : Y.Opens) :
    Γ(Scheme.Hom.relativeDifferentials p,U) →ₛₗ[(g.app U).hom]
      Γ(Scheme.Hom.relativeDifferentials (g ≫ p),g ⁻¹ᵁ U) :=
  (((differentialMap g p).val.app (op (g ⁻¹ᵁ U))).hom).comp
    (pullbackSections g (Scheme.Hom.relativeDifferentials p) U)

/-- The true native derivative map sends the original differential of
an actual function to the differential of its actual pullback. -/
theorem differentialSections_d (g : X ⟶ Y) (p : Y ⟶ S) (U : Y.Opens) (r : Γ(Y,U)) :
    differentialSections g p U (localDerivation p U r)=
      localDerivation (g ≫ p) (g ⁻¹ᵁ U) ((g.app U).hom r) :=
  Scheme.Hom.relativeDifferentialsMap_app_d (f := g) (p := p) (p' := g ≫ p)
    (𝟙 S) (Category.comp_id (g ≫ p)).symm U r

/-- The actual dual pullback unit, followed by the actual dual
base-change morphism. No dual base-change invertibility is assumed. -/
def dualSections (g : X ⟶ Y) (Q : Y.Modules) (U : Y.Opens) :
    Γ(dualSheaf Q,U) →ₛₗ[(g.app U).hom]
      Γ(dualSheaf ((Scheme.Modules.pullback g).obj Q),g ⁻¹ᵁ U) :=
  (((Stacks.Chow.pullbackDualMap g Q).val.app (op (g ⁻¹ᵁ U))).hom).comp
    (pullbackSections g (dualSheaf Q) U)

theorem coefficientMap_dualSections (g : X ⟶ Y) (q : freeOn Y 6 ⟶ Q)
    (U : Y.Opens) (α : Γ(dualSheaf Q,U)) (j : Fin 6) :
    coefficientMap (pulledQuotient g q) (g ⁻¹ᵁ U) (dualSections g Q U α) j=
      (g.app U).hom (coefficientMap q U α j) :=
  coefficientMap_pullback_unit g q U α j

/-- The actual intrinsic bilinear form commutes with the original
native derivative map and actual dual pullback. -/
theorem localPairing_pullback (g : X ⟶ Y) (p : Y ⟶ S) (q : freeOn Y 6 ⟶ Q)
    (hq : AnnihilatesSigma Y q) (U : Y.Opens) (α β : Γ(dualSheaf Q,U)) :
    differentialSections g p U (localPairing p q hq U α β)=
      localPairing (g ≫ p) (pulledQuotient g q) (pulledQuotient_annihilates g q hq)
        (g ⁻¹ᵁ U) (dualSections g Q U α) (dualSections g Q U β) := by
  change differentialSections g p U (differentialPair (localDerivation p U)
    (coefficientMap q U) α β)=
      differentialPair (localDerivation (g ≫ p) (g ⁻¹ᵁ U))
        (coefficientMap (pulledQuotient g q) (g ⁻¹ᵁ U))
        (dualSections g Q U α) (dualSections g Q U β)
  simp only [differentialPair,map_sum,map_sub,map_smulₛₗ,differentialSections_d,
    coefficientMap_dualSections]

/-- The genuine local symmetric-power lift commutes with the actual
semilinear pullback maps, including all original coefficient rings. -/
theorem localSquareMap_pullback (g : X ⟶ Y) (p : Y ⟶ S) (q : freeOn Y 6 ⟶ Q)
    (hq : AnnihilatesSigma Y q) (U : Y.Opens)
    (z : SymPow.symmetricPower 2 Γ(Y,U) Γ(dualSheaf Q,U)) :
    differentialSections g p U (localSquareMap p q hq U z)=
      localSquareMap (g ≫ p) (pulledQuotient g q) (pulledQuotient_annihilates g q hq)
        (g ⁻¹ᵁ U) (SymPow.symMapₛₗ 2 (g.app U).hom (dualSections g Q U) z) :=
  sqLift_naturality (R := Γ(Y,U)) (S := Γ(X,g ⁻¹ᵁ U)) (g.app U).hom
    (dualSections g Q U) (differentialSections g p U) _ _ _ _
      (localPairing_pullback g p q hq U) z

end M9Native.LagrangianCotangentPullbackNaturality

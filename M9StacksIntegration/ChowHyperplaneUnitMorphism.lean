module

public import M9StacksIntegration.ChowHyperplanePieces

/-! The original arbitrary-pieces hyperplane is identified by its
actual unit-to-line morphism. This keeps the original categorical
quotient and does not ask for a cross-model Gamma coordinate formula. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.Scheme.unitModule
  SheafOfModules.unit PresheafOfModules.unit
namespace M9Native.ChowHyperplaneUnitMorphism
open ChowHyperplanePieces

variable {X : Scheme.{u}} (F : X.Modules) (hqc : Stacks.SymGraded.IsQuasicoherentPieces F)
  (sigma : Scheme.unitModule X ⟶ F)

theorem originalSection_unitHom :
    Scheme.Modules.unitHomEquivTop (twist F hqc) (originalSection F hqc sigma) =
      (Scheme.Modules.pullbackUnitIso (projection F hqc)).inv ≫
        (Scheme.Modules.pullback (projection F hqc)).map sigma ≫ tautological F hqc := by
  have hs : Scheme.Modules.unitHomEquivTop F (sigma.app ⊤ (1 : Γ(X,⊤))) = sigma := by
    apply LagrangianSectionGeneration.unitHom_ext_top_one
    exact LagrangianAffineDeterminant.unitHom_top_one F _
  exact (QuotientSectionMorphism.unitHom_quotient (projection F hqc) F (twist F hqc)
    (tautological F hqc) _).trans
      (congrArg (fun z => (Scheme.Modules.pullbackUnitIso (projection F hqc)).inv ≫
        (Scheme.Modules.pullback (projection F hqc)).map z ≫ tautological F hqc) hs)

end M9Native.ChowHyperplaneUnitMorphism

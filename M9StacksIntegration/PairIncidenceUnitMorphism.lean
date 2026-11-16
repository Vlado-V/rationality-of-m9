module

public import M9StacksIntegration.PairTensorUnitMorphism
public import M9StacksIntegration.TensorPairingTopComparison

/-! Both native presentations of a pair tensor have the SAME actual
unit-to-module morphism. The canonical quotient and canonical pullback
are retained as parameters, so no cross-model Gamma equality is needed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.PairIncidenceUnitMorphism
open LagrangianMatrixChart LinearIncidenceTensorCoordinates TensorUnitSections

private theorem unitHom_pairing {P : Scheme.{u}} (A L : P.Modules)
    (s : Γ(A,⊤)) (t : Γ(L,⊤)) :
    Scheme.Modules.unitHomEquivTop (tensorObj P A L)
      (Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf P.sheaf)
        (Stacks.SheafOfModules.tensorSectionPairing (O := P.sheaf) A L) (op ⊤) s t) =
      Scheme.Modules.unitHomEquivTop L t ≫ (unitTensorIso P L).inv ≫
        tensorFirst (Scheme.Modules.unitHomEquivTop A s) L := by
  rw [TensorPairingTopComparison.pairing_eq_tensorTop,unitHom_tensorTop]

variable {X P : Scheme.{u}} (p : P ⟶ X) (E : X.Modules) (L : P.Modules)
  (tau : (Scheme.Modules.pullback p).obj (freeOn X 2) ⟶ L) (s : Fin 2 → Γ(E,⊤))

def columnMap (k : Fin 2) : Scheme.unitModule P ⟶ (Scheme.Modules.pullback p).obj E :=
  (Scheme.Modules.pullbackUnitIso p).inv ≫
    (Scheme.Modules.pullback p).map (Scheme.Modules.unitHomEquivTop E (s k))

def termMap (k : Fin 2) : Scheme.unitModule P ⟶ tensorObj P ((Scheme.Modules.pullback p).obj E) L :=
  PairTensorUnitMorphism.coordinateMap p L tau k ≫ (unitTensorIso P L).inv ≫
    tensorFirst (columnMap p E s k) L

def tensorTerm (k : Fin 2) : Γ(tensorObj P ((Scheme.Modules.pullback p).obj E) L,⊤) :=
  tensorTop P ((Scheme.Modules.pullback p).obj E) L
    (pullbackGlobalSections p E (s k)) (PairTensorUnitMorphism.coordinate p L tau k)

def pairingTerm (k : Fin 2) : Γ(tensorObj P ((Scheme.Modules.pullback p).obj E) L,⊤) :=
  Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf P.sheaf)
    (Stacks.SheafOfModules.tensorSectionPairing (O := P.sheaf) ((Scheme.Modules.pullback p).obj E) L)
    (op ⊤) (pullbackGlobalSections p E (s k)) (PairTensorUnitMorphism.coordinate p L tau k)

theorem tensorTerm_unitHom (k : Fin 2) :
    Scheme.Modules.unitHomEquivTop (tensorObj P ((Scheme.Modules.pullback p).obj E) L)
      (tensorTerm p E L tau s k) = termMap p E L tau s k := by
  rw [tensorTerm,unitHom_tensorTop,PairTensorUnitMorphism.coordinate_unitHom,
    ChowSplitLineProjectiveZero.unitHom_pullback]
  rfl

theorem pairingTerm_unitHom (k : Fin 2) :
    Scheme.Modules.unitHomEquivTop (tensorObj P ((Scheme.Modules.pullback p).obj E) L)
      (pairingTerm p E L tau s k) = termMap p E L tau s k := by
  rw [pairingTerm,unitHom_pairing,PairTensorUnitMorphism.coordinate_unitHom,
    ChowSplitLineProjectiveZero.unitHom_pullback]
  rfl

theorem tensorSum_unitHom :
    Scheme.Modules.unitHomEquivTop (tensorObj P ((Scheme.Modules.pullback p).obj E) L)
      (∑ k : Fin 2, tensorTerm p E L tau s k) =
      termMap p E L tau s 0 + termMap p E L tau s 1 := by
  rw [Fin.sum_univ_two,unitHom_add,tensorTerm_unitHom,tensorTerm_unitHom]

theorem pairingSum_unitHom :
    Scheme.Modules.unitHomEquivTop (tensorObj P ((Scheme.Modules.pullback p).obj E) L)
      (∑ k : Fin 2, pairingTerm p E L tau s k) =
      termMap p E L tau s 0 + termMap p E L tau s 1 := by
  rw [Fin.sum_univ_two,unitHom_add,pairingTerm_unitHom,pairingTerm_unitHom]

end M9Native.PairIncidenceUnitMorphism

module

public import M9StacksIntegration.TensorUnitSections
public import M9StacksIntegration.FreeTwoSplitHyperplane

/-! The actual two-term incidence tensor is the image of the actual
unit-row hyperplane, first as a unit-to-module morphism. The proof is
parametric in the actual scheme P and its actual quotient tau, so it
does not compare global-section dictionaries of two Proj models. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.Scheme.unitModule
  SheafOfModules.unit PresheafOfModules.unit

namespace M9Native.PairTensorUnitMorphism
open LagrangianMatrixChart LinearIncidenceTensorCoordinates TensorUnitSections

private theorem unitHom_top_value {Y : Scheme.{u}} (A : Y.Modules)
    (a : Scheme.unitModule Y ⟶ A) :
    Scheme.Modules.unitHomEquivTop A (a.app ⊤ (1 : Γ(Y,⊤)))=a := by
  apply LagrangianSectionGeneration.unitHom_ext_top_one
  exact LagrangianAffineDeterminant.unitHom_top_one A _

private theorem pulled_unit_value {X P : Scheme.{u}} (p : P ⟶ X) (A : X.Modules)
    (a : Scheme.unitModule X ⟶ A) :
    Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback p).obj A)
        (pullbackGlobalSections p A (a.app ⊤ (1 : Γ(X,⊤)))) =
      (Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map a := by
  exact (ChowSplitLineProjectiveZero.unitHom_pullback p A _).trans
    (congrArg (fun z => (Scheme.Modules.pullbackUnitIso p).inv ≫
      (Scheme.Modules.pullback p).map z) (unitHom_top_value A a))

variable {X P : Scheme.{u}} (p : P ⟶ X) (F : X.Modules) (L : P.Modules)
  (τ : (Scheme.Modules.pullback p).obj (freeOn X 2) ⟶ L)
  (j : Scheme.unitModule X ⟶ F) (t : Scheme.unitModule X ⟶ Scheme.unitModule X)
  (i : Fin 2)

def column : Scheme.unitModule P ⟶ (Scheme.Modules.pullback p).obj F :=
  (Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map j

def scalarMap : Scheme.unitModule P ⟶ Scheme.unitModule P :=
  (Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map t ≫
    (Scheme.Modules.pullbackUnitIso p).hom

def imageMap : L ⟶ tensorObj P ((Scheme.Modules.pullback p).obj F) L :=
  (unitTensorIso P L).inv ≫ tensorFirst (column p F j) L

def coordinate (k : Fin 2) : Γ(L,⊤) :=
  τ.app ⊤ (pullbackGlobalSections p (freeOn X 2) (freeBasisSection X 2 k))

def coordinateMap (k : Fin 2) : Scheme.unitModule P ⟶ L :=
  (Scheme.Modules.pullbackUnitIso p).inv ≫
    (Scheme.Modules.pullback p).map (FreeTwoCoordinates.inclusion X k) ≫ τ

def basePair (k : Fin 2) : Scheme.unitModule X ⟶ F := if k=i then j else t ≫ j

def term (k : Fin 2) : Γ(tensorObj P ((Scheme.Modules.pullback p).obj F) L,⊤) :=
  tensorTop P ((Scheme.Modules.pullback p).obj F) L
    (pullbackGlobalSections p F ((basePair F j t i k).app ⊤ (1 : Γ(X,⊤))))
    (coordinate p L τ k)

def equation : Γ(tensorObj P ((Scheme.Modules.pullback p).obj F) L,⊤) :=
  ∑ k : Fin 2, term p F L τ j t i k

def hyperplaneMap : Scheme.unitModule P ⟶ L :=
  (Scheme.Modules.pullbackUnitIso p).inv ≫
    (Scheme.Modules.pullback p).map (FreeTwoSplitHyperplane.subline X t i) ≫ τ

theorem coordinate_unitHom (k : Fin 2) :
    Scheme.Modules.unitHomEquivTop L (coordinate p L τ k)=coordinateMap p L τ k := by
  have hb : Scheme.Modules.unitHomEquivTop (freeOn X 2) (freeBasisSection X 2 k) =
      FreeTwoCoordinates.inclusion X k := unitHom_top_value (freeOn X 2) _
  exact (QuotientSectionMorphism.unitHom_quotient p (freeOn X 2) L τ _).trans
    (congrArg (fun z => (Scheme.Modules.pullbackUnitIso p).inv ≫
      (Scheme.Modules.pullback p).map z ≫ τ) hb)

theorem column_composite :
    (Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map (t ≫ j) =
      scalarMap p t ≫ column p F j := by
  simp [scalarMap,column,Functor.map_comp,Category.assoc]

theorem hyperplaneMap_eq : hyperplaneMap p L τ t i =
    coordinateMap p L τ i + scalarMap p t ≫ coordinateMap p L τ (FreeTwoCoordinates.other i) := by
  simp [hyperplaneMap,FreeTwoSplitHyperplane.subline,coordinateMap,scalarMap,
    Functor.map_add,Functor.map_comp,Preadditive.comp_add,Preadditive.add_comp,Category.assoc]

theorem term_unitHom (k : Fin 2) :
    Scheme.Modules.unitHomEquivTop (tensorObj P ((Scheme.Modules.pullback p).obj F) L)
        (term p F L τ j t i k) =
      (if k=i then coordinateMap p L τ k else scalarMap p t ≫ coordinateMap p L τ k) ≫
        imageMap p F L j := by
  rw [term,unitHom_tensorTop,coordinate_unitHom,pulled_unit_value]
  by_cases hk : k=i
  · simp only [basePair,hk,ite_true,column,imageMap,Category.assoc]
  · simp only [basePair,hk,ite_false]
    rw [column_composite]
    change coordinateMap p L τ k ≫ (unitTensorIso P L).inv ≫
        tensorFirst (scalarMap p t ≫ column p F j) L = _
    rw [tensorFirst,Functor.map_comp]
    change coordinateMap p L τ k ≫ (unitTensorIso P L).inv ≫
        tensorFirst (scalarMap p t) L ≫ tensorFirst (column p F j) L = _
    rw [reassoc_of% (unit_tensor_central L (scalarMap p t) (coordinateMap p L τ k))]
    rfl

/-- The genuine incidence section has the genuine hyperplane image
unit-map, with no covariance or section-equality premise. -/
theorem equation_unitHom :
    Scheme.Modules.unitHomEquivTop (tensorObj P ((Scheme.Modules.pullback p).obj F) L)
        (equation p F L τ j t i) =
      hyperplaneMap p L τ t i ≫ imageMap p F L j := by
  simp only [equation,Fin.sum_univ_two]
  rw [unitHom_add,term_unitHom,term_unitHom,hyperplaneMap_eq]
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl | rfl <;>
    simp [FreeTwoCoordinates.other,Preadditive.add_comp,Category.assoc,add_comm]

end M9Native.PairTensorUnitMorphism

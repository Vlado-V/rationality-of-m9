module

public import M9StacksIntegration.MukaiWedgeDuality
public import M9StacksIntegration.MukaiHomCoefficient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# The actual rank-two determinant pairing with a coefficient sheaf

The native perfect rank-two wedge pairing and the proved coefficient
comparison construct `N tensor C = Hom(C,Omega)` from the actual
identification `N tensor exteriorSquare C = Omega`. Its contraction by
every genuine section is minus tensoring the literal wedge morphism.
No self-duality or alternating cohomology form is supplied as data.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace M9Native.MukaiWedgeSelfDual

open M9Native.MukaiCupAlternating M9Native.MukaiHomExact
open M9Native.MukaiTensorSection M9Native.MukaiHomCoefficient
open M9Native.MukaiWedgeDuality

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- Adjunction evaluation is the actual section-evaluation morphism
already used to identify the native rank-two wedge pairing. -/
theorem evaluation_eq_evaluateSection (C D : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ C) :
    evaluation C s D = evaluateSection C D (C.unitHomEquiv s) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext φ
  exact adjunctionEvaluation_app C D s U φ

/-- Literal evaluation commutes with the actual coefficient morphism. -/
theorem evaluation_naturality (C : X.Modules) {D W : X.Modules}
    (g : D ⟶ W) (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ C) :
    (homFunctor C).map g ≫ evaluation C s W = evaluation C s D ≫ g := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext φ
  rw [_root_.SheafOfModules.comp_val_app_apply,
    _root_.SheafOfModules.comp_val_app_apply]
  refine Eq.trans (adjunctionEvaluation_app C W s U (((homFunctor C).map g).val.app U φ)) ?_
  refine Eq.trans (show
    Stacks.SheafOfModules.evalSection X.sheaf.obj C.val W.val U
      (((homFunctor C).map g).val.app U φ) ((C.unitHomEquiv s).val U) =
      g.val.app U (Stacks.SheafOfModules.evalSection X.sheaf.obj C.val D.val U
        φ ((C.unitHomEquiv s).val U)) from rfl) ?_
  exact congrArg (fun z => g.val.app U z) (adjunctionEvaluation_app C D s U φ).symm

/-- The actual coefficient-twisted perfect rank-two wedge pairing,
constructed from the native wedge isomorphism and actual determinant data. -/
def tensorWedgeHomIso (C N Ω : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    (d : tensor N (exteriorSquare C) ≅ Ω) :
    tensor N C ≅ (homFunctor C).obj Ω :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).mapIso
      (rankTwoWedgeIso C hC) ≪≫
    homCoefficientIso C 2 hC N (exteriorSquare C) ≪≫
      (homFunctor C).mapIso d

/-- Its actual contraction at a section is the negative of the original
tensor-wedge map, with no alternating-pairing premise. -/
theorem tensorWedgeHomIso_evaluation (C N Ω : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    (d : tensor N (exteriorSquare C) ≅ Ω)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ C) :
    (tensorWedgeHomIso C N Ω hC d).hom ≫ evaluation C s Ω =
      -(tensorWedgeMap C s N ≫ d.hom) := by
  let T : X.Modules ⥤ X.Modules :=
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N
  let : T.Additive :=
    Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive X.sheaf N
  have hc : (rankTwoWedgeIso C hC).hom ≫ evaluation C s (exteriorSquare C) =
      -wedgeBySection C (C.unitHomEquiv s) := by
    rw [evaluation_eq_evaluateSection]
    exact rankTwoWedgeIso_comp_evaluateSection C hC (C.unitHomEquiv s)
  change (T.map (rankTwoWedgeIso C hC).hom ≫
    (homCoefficientIso C 2 hC N (exteriorSquare C)).hom ≫
      (homFunctor C).map d.hom) ≫ evaluation C s Ω = _
  rw [Category.assoc, Category.assoc, evaluation_naturality C d.hom s,
    ← Category.assoc (homCoefficientIso C 2 hC N (exteriorSquare C)).hom,
    homCoefficientIso_evaluation C 2 hC N (exteriorSquare C) s]
  change T.map (rankTwoWedgeIso C hC).hom ≫
      (T.map (evaluation C s (exteriorSquare C)) ≫ d.hom) = _
  rw [← Category.assoc, ← T.map_comp, hc, T.map_neg, Preadditive.neg_comp]
  rfl

end M9Native.MukaiWedgeSelfDual

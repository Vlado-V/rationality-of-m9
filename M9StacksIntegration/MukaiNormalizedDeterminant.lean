module

public import M9StacksIntegration.MukaiNormalizedFiltration
public import M9StacksIntegration.ExteriorTensorLine
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant

/-!
# The normalized determinant from the original genuine line filtration

The actual short exact line filtration identifies `L tensor M` with
the actual second exterior power of its middle bundle. The tensor-line
exterior-square isomorphism and actual inverse-tensor cancellation then
construct the coefficient determinant from the original determinant
relation. The coefficient determinant is not an additional premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.MukaiNormalizedDeterminant

open M9Native.MukaiCupAlternating M9Native.MukaiHomCoefficient
open M9Native.MukaiNormalizedFiltration

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The genuine line filtration has its actual top-exterior
identification by the native comparison for the actual short exact sequence. -/
def lineFiltrationExteriorIso {L F M : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (i : L ⟶ F) (q : F ⟶ M) (w : i ≫ q = 0)
    (hS : (ShortComplex.mk i q w).ShortExact) :
    tensor L M ≅ exteriorSquare F := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M)
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X M
  let T : X.Modules ⥤ X.Modules ⥤ X.Modules :=
    Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf
  exact (T.mapIso (Scheme.Modules.exteriorPowerOneIsoSelf L).symm).app M ≪≫
    (T.obj (Scheme.Modules.exteriorPower L 1)).mapIso
      (Scheme.Modules.exteriorPowerOneIsoSelf M).symm ≪≫
    Scheme.Modules.exteriorPowerTensorExteriorPowerIso i q w hS 1 0

/-- The coefficient determinant of the normalized tensor sequence
follows from the actual original determinant relation and actual filtration. -/
def normalizedDeterminantIso (E Ω : X.Modules) {L F M : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (i : L ⟶ F) (q : F ⟶ M) (w : i ≫ q = 0)
    (hS : (ShortComplex.mk i q w).ShortExact)
    (d : tensor (exteriorSquare E) (exteriorSquare F) ≅ Ω) :
    tensor (tensor L (inverseLine M)) (exteriorSquare (tensor E M)) ≅ Ω := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M)
  let T : X.Modules ⥤ X.Modules ⥤ X.Modules :=
    Stacks.SheafOfModules.Tensor.sheafTensor.{u,u,u,u,u} X.sheaf
  let N := tensor L (inverseLine M)
  let D := exteriorSquare E
  exact (T.obj N).mapIso (M9Native.ExteriorTensorLine.exteriorTensorLineIso E M) ≪≫
    (T.obj N).mapIso (tensorAssociator D M M).symm ≪≫
    (tensorAssociator N (tensor D M) M).symm ≪≫
    (T.mapIso (normalizedTensorMiddleIso D L M)).app M ≪≫
    tensorAssociator D L M ≪≫
    (T.obj D).mapIso (lineFiltrationExteriorIso i q w hS) ≪≫ d

end M9Native.MukaiNormalizedDeterminant

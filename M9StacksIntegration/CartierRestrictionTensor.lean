module

public import M9StacksIntegration.PoincareProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# Actual invertible twists of the Cartier sum sequence

The named native Cartier sum sequence is tensored by an actual
invertible module. Its middle and right terms are identified with
the ordinary images of the actual restrictions; its left term is
the ordinary image of the restricted normal line tensored with the
restricted module. No exactness, splitting, or image-filtration
premise is supplied.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.CartierRestrictionTensor

variable {Y : Scheme.{u}} (D C : Y.IdealSheafData) (L : Y.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]

/-- Actual tensor with a closed structure module is the ordinary image
of the actual restriction. -/
def tensorClosedStructureIso :
    Scheme.Modules.tensorObj (Scheme.IdealSheafData.closedSubschemeStructureSheaf D) L ≅
      (Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj L) :=
  PoincareChern.invertibleOrdinaryProjectionFormulaIso D.subschemeι
    (SheafOfModules.unit D.subscheme.ringCatSheaf) L ≪≫
  (Scheme.Modules.pushforward D.subschemeι).mapIso
    (Scheme.Modules.tensorObjLeftUnitor _)

/-- The actual kernel term has the actual restricted normal line. -/
def tensorSumKernelIso :
    Scheme.Modules.tensorObj
      ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Divisors.negativeTwist D))) L ≅
      (Scheme.Modules.pushforward C.subschemeι).obj
        (Scheme.Modules.tensorObj
          ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Divisors.negativeTwist D))
          ((Scheme.Modules.pullback C.subschemeι).obj L)) :=
  PoincareChern.invertibleOrdinaryProjectionFormulaIso C.subschemeι _ L

/-- Actual maps and short exactness after tensoring the genuine
Cartier sum sequence; the product is literally `C * D`. -/
theorem exists_tensorSum_shortExact
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) :
    ∃ (i : Scheme.Modules.tensorObj
        ((Scheme.Modules.pushforward C.subschemeι).obj
          ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Divisors.negativeTwist D))) L ⟶
        Scheme.Modules.tensorObj
          (Scheme.IdealSheafData.closedSubschemeStructureSheaf (C * D)) L)
      (p : Scheme.Modules.tensorObj
          (Scheme.IdealSheafData.closedSubschemeStructureSheaf (C * D)) L ⟶
        Scheme.Modules.tensorObj (Scheme.IdealSheafData.closedSubschemeStructureSheaf D) L)
      (w : i ≫ p = 0), (ShortComplex.mk i p w).ShortExact := by
  let S := ShortComplex.mk (Stacks.Divisors.sumKernelMap D C hD)
    (Scheme.IdealSheafData.closedSubschemeRestriction hsub)
    (Stacks.Divisors.sumKernelMap_comp_closedSubschemeRestriction D C hD hsub)
  have hS : S.ShortExact := Stacks.Divisors.shortExact_sumKernelMap D C hD hsub
  have := hS.mono_f
  have := hS.epi_g
  have hLa : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hL
  have hR := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible Y L hLa
  let : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := Y.ringCatSheaf) L :=
    Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree L
      (hM := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1 (hM := hR))
  exact Scheme.Modules.tensorObj_shortExact S.f S.g S.zero hS.exact L
    (Scheme.Modules.isFlat_of_isFiniteLocallyFree L)

end M9Native.CartierRestrictionTensor

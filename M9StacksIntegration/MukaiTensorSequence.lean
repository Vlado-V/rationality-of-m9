module

public import M9StacksIntegration.MukaiTensorDiagonal
public import M9StacksIntegration.MukaiHomCoefficient
public import M9StacksIntegration.InvertibleExtCancellation
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts

/-!
# The actual normalized tensor sequence and its original Yoneda class

Exactness follows from genuine finite local freeness. The middle rank
follows from the actual extension of two lines. Its actual pulled-back
tensor extension has zero wedge postcomposition by the checked diagonal.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u w

namespace M9Native.MukaiTensorSequence

open M9Native.MukaiCupAlternating M9Native.MukaiHomCoefficient
open M9Native.MukaiTensorSection M9Native.MukaiTensorDiagonal
open M9Native.InvertibleExtCancellation (unit)

variable {X : Scheme.{u}}

/-- The original actual short complex tensored by the original bundle. -/
def tensorSequence (C : X.Modules) (S : ShortComplex X.Modules) :
    ShortComplex X.Modules := by
  letI := tensorRight_additive C
  exact S.map (tensorRight C)

/-- Actual finite local freeness proves exactness of the actual tensor
sequence, without a supplied image-exactness witness. -/
theorem tensorSequence_shortExact (C : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFree.{u,u,u} C)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (tensorSequence C S).ShortExact := by
  let := tensorRight_additive C
  let : PreservesFiniteLimits (tensorRight C) := (tensorRight_exact C hC).1
  let : PreservesFiniteColimits (tensorRight C) := (tensorRight_exact C hC).2
  exact hS.map_of_exact (tensorRight C)

/-- The genuine middle bundle of the actual line extension has rank two. -/
theorem extensionMiddle_rank {N B : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (i : N ⟶ B) (q : B ⟶ (unit X)) (w : i ≫ q = 0)
    (hS : (ShortComplex.mk i q w).ShortExact) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 2 := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N :=
    inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N)
  exact Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
    (ShortComplex.mk i q w) hS 1 1
    (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X N)
    (SheafOfModules.isFiniteLocallyFreeOfRank_unit X)

section Ext

variable [HasExt.{w} X.Modules]

/-- The actual tensor extension pulled back by the actual natural section. -/
def sectionExtensionClass (C : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFree.{u,u,u} C)
    {N : X.Modules} {n : ℕ} (ξ : Ext.{w} (C := X.Modules) (unit X) N n)
    (s : unit X ⟶ C) :
    Ext.{w} (C := X.Modules) (unit X) (tensor N C) n := by
  letI := tensorRight_additive C
  letI : PreservesFiniteLimits (tensorRight C) := (tensorRight_exact C hC).1
  letI : PreservesFiniteColimits (tensorRight C) := (tensorRight_exact C hC).2
  exact (Ext.mk₀ ((tensorSection C s).app (unit X))).comp
    (ξ.mapExactFunctor (tensorRight C)) (zero_add n)

/-- Its literal wedge coefficient postcomposition vanishes by genuine
exterior square-zero and actual Yoneda functoriality. -/
theorem sectionExtensionClass_wedge_zero (C : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFree.{u,u,u} C)
    {N : X.Modules} {n : ℕ} (ξ : Ext.{w} (C := X.Modules) (unit X) N n)
    (s : unit X ⟶ C) :
    (sectionExtensionClass C hC ξ s).comp
      (Ext.mk₀ (tensorWedgeMap C s N)) (add_zero n) = 0 :=
  tensorSectionExt_wedge_diagonal_eq_zero C hC ξ s

end Ext

end M9Native.MukaiTensorSequence

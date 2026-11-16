module

public import M9StacksIntegration.SplitPairTensorZero
public import M9StacksIntegration.RankTwoUnitPivotColumns
public import M9StacksIntegration.FreeTwoPairIncidence

/-! A determinant-zero original selected pair with a genuine unit pivot
has full scheme-theoretic incidence isomorphic to its base. The actual
split line and its retraction are constructed from the original matrix. -/

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
namespace M9Native.FreeTwoSelectedPairIso
open LagrangianMatrixChart FreeTwoProjectiveCharts

variable (X : Scheme.{u}) {F : X.Modules}
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
  (eF : F ≅ freeOn X 2) (s : Fin 2 → Γ(F,⊤)) (row col : Fin 2) (a : Γ(X,⊤)ˣ)
  (hdet : (RankTwoUnitPivotColumns.sectionMatrix X eF s).det = 0)
  (ha : RankTwoUnitPivotColumns.sectionMatrix X eF s row col = (a : Γ(X,⊤)))

include hdet ha in
private theorem sections_eq (k : Fin 2) :
    s k = (PairTensorUnitMorphism.basePair F
      (RankTwoUnitPivotColumns.subline X s col)
      (RankTwoUnitPivotColumns.scalarMap X eF s row col a) col k).app ⊤ (1 : Γ(X,⊤)) := by
  have h := RankTwoUnitPivotColumns.original_pair_eq X eF s row col a hdet ha k
  by_cases hk : k=col
  · simpa only [PairTensorUnitMorphism.basePair,hk,ite_true] using h
  · simp only [PairTensorUnitMorphism.basePair,hk,ite_false]
    change s k = (RankTwoUnitPivotColumns.subline X s col).app ⊤
      ((RankTwoUnitPivotColumns.scalarMap X eF s row col a).app ⊤ (1 : Γ(X,⊤)))
    simpa only [hk,ite_false] using h

include hdet ha in
theorem equationSection_eq : FreeTwoPairIncidence.equationSection X F s =
    SplitPairTensorZero.equation X F (RankTwoUnitPivotColumns.subline X s col)
      (RankTwoUnitPivotColumns.scalarMap X eF s row col a) col := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [sections_eq X eF s row col a hdet ha k]
  rfl

include hdet ha in
theorem ideal_eq : FreeTwoPairIncidence.ideal X F s =
    SplitPairTensorZero.zeroIdeal X F (RankTwoUnitPivotColumns.subline X s col)
      (RankTwoUnitPivotColumns.scalarMap X eF s row col a) col := by
  exact congrArg (SectionZeroIdealFactorization.sectionZeroIdeal
    (projectiveBundleSpace X) (FreeTwoPairIncidence.equationBundle X F))
      (equationSection_eq X eF s row col a hdet ha)

def zeroIsoBase : FreeTwoPairIncidence.space X F s ≅ X :=
  eqToIso (congrArg (fun I : (projectiveBundleSpace X).IdealSheafData => I.subscheme)
    (ideal_eq X eF s row col a hdet ha)) ≪≫
  SplitPairTensorZero.zeroIsoBase X F (RankTwoUnitPivotColumns.subline X s col)
    (RankTwoUnitPivotColumns.retraction X eF row a)
    (RankTwoUnitPivotColumns.subline_retraction X eF s row col a ha)
    (RankTwoUnitPivotColumns.scalarMap X eF s row col a) col

theorem zeroIsoBase_hom : (zeroIsoBase X eF s row col a hdet ha).hom =
    FreeTwoPairIncidence.toBase X F s := by
  rw [zeroIsoBase,Iso.trans_hom,SplitPairTensorZero.zeroIsoBase_hom,← Category.assoc]
  exact congrArg (· ≫ projectiveBundleProjection X)
    (LagrangianMatrixChart.eqToIso_subscheme_ι _ _ (ideal_eq X eF s row col a hdet ha))

include hdet ha in
theorem projection_isIso : IsIso (FreeTwoPairIncidence.toBase X F s) := by
  rw [← zeroIsoBase_hom X eF s row col a hdet ha]
  infer_instance

end M9Native.FreeTwoSelectedPairIso

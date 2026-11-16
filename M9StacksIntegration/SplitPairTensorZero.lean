module

public import M9StacksIntegration.PairTensorZeroIdeal
public import M9StacksIntegration.ChowHyperplaneUnitMorphism

/-! The ORIGINAL projective incidence of a genuine split image pair is
actually isomorphic to its base. Equality of FULL ideals is derived
from the unit-map identity on all test schemes, preserving nilpotents. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.SplitPairTensorZero
open LagrangianMatrixChart FreeTwoProjectiveCharts LinearIncidenceTensorCoordinates

variable (X : Scheme.{u}) (F : X.Modules)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
  (j : Scheme.unitModule X ⟶ F) (r : F ⟶ Scheme.unitModule X)
  (hret : j ≫ r = 𝟙 (Scheme.unitModule X))
  (t : Scheme.unitModule X ⟶ Scheme.unitModule X) (i : Fin 2)

abbrev tautological :
    (Scheme.Modules.pullback (projectiveBundleProjection X)).obj (freeOn X 2) ⟶
      tautologicalLine X := Stacks.Chow.bundleTautological (freeOn X 2)

instance line_rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tautologicalLine X) 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (projectiveBundleSpace X) (tautologicalLine X)
    (Stacks.Chow.isInvertible_bundleTwist (freeOn X 2))

abbrev equation := PairTensorUnitMorphism.equation (projectiveBundleProjection X) F
  (tautologicalLine X) (tautological X) j t i

abbrev zeroIdeal := PairTensorZeroIdeal.vectorIdeal (projectiveBundleProjection X) F
  (tautologicalLine X) (tautological X) j t i

include r hret in
theorem zeroIdeal_eq_hyperplane : zeroIdeal X F j t i = FreeTwoSplitHyperplane.zeroIdeal X t i := by
  letI := isFiniteLocallyFreeOfRank_pullback (projectiveBundleProjection X) F 2
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (tensorObj (projectiveBundleSpace X)
        ((Scheme.Modules.pullback (projectiveBundleProjection X)).obj F) (tautologicalLine X)) 2 := by
    exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf
      (projectiveBundleSpace X) ((Scheme.Modules.pullback (projectiveBundleProjection X)).obj F)
        (tautologicalLine X) 2 1
  apply SectionZeroSubbundle.ideal_eq_of_all_factors
  intro T f
  change (∃ a : T ⟶ (SectionZeroIdealFactorization.sectionZeroIdeal (projectiveBundleSpace X) _
      (equation X F j t i)).subscheme,
      a ≫ (SectionZeroIdealFactorization.sectionZeroIdeal (projectiveBundleSpace X) _
        (equation X F j t i)).subschemeι=f) ↔ _
  rw [← SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (tensorObj (projectiveBundleSpace X)
      ((Scheme.Modules.pullback (projectiveBundleProjection X)).obj F) (tautologicalLine X))
      2 (equation X F j t i) f]
  change _ ↔ ∃ a : T ⟶ (SectionZeroIdealFactorization.sectionZeroIdeal
      (projectiveBundleSpace X) (tautologicalLine X)
      (FreeTwoSplitHyperplane.originalSection X t i)).subscheme,
      a ≫ (SectionZeroIdealFactorization.sectionZeroIdeal
        (projectiveBundleSpace X) (tautologicalLine X)
        (FreeTwoSplitHyperplane.originalSection X t i)).subschemeι=f
  rw [← SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (tautologicalLine X) 1 (FreeTwoSplitHyperplane.originalSection X t i) f,
    SplitLineProjectiveZero.pullback_section_eq_zero_iff,
    SplitLineProjectiveZero.pullback_section_eq_zero_iff]
  have he := PairTensorUnitMorphism.equation_unitHom (projectiveBundleProjection X) F
    (tautologicalLine X) (tautological X) j t i
  rw [show Scheme.Modules.unitHomEquivTop (tautologicalLine X)
      (FreeTwoSplitHyperplane.originalSection X t i) =
        PairTensorUnitMorphism.hyperplaneMap (projectiveBundleProjection X)
          (tautologicalLine X) (tautological X) t i from
    ChowHyperplaneUnitMorphism.originalSection_unitHom (freeOn X 2)
      (Stacks.Chow.bundlePieces (freeOn X 2)) (FreeTwoSplitHyperplane.subline X t i)]
  rw [he,Functor.map_comp]
  letI := PairTensorZeroIdeal.imageMap_universallyMono (projectiveBundleProjection X) F
    (tautologicalLine X) j r hret f
  constructor
  · intro h
    exact (cancel_mono ((Scheme.Modules.pullback f).map
      (PairTensorUnitMorphism.imageMap (projectiveBundleProjection X) F
        (tautologicalLine X) j))).mp (by simpa using h)
  · intro h
    rw [h,zero_comp]

def zeroIsoBase : (zeroIdeal X F j t i).subscheme ≅ X :=
  eqToIso (congrArg (fun I : (projectiveBundleSpace X).IdealSheafData => I.subscheme)
    (zeroIdeal_eq_hyperplane X F j r hret t i)) ≪≫ FreeTwoSplitHyperplane.zeroIsoBase X t i

theorem zeroIsoBase_hom : (zeroIsoBase X F j r hret t i).hom =
    (zeroIdeal X F j t i).subschemeι ≫ projectiveBundleProjection X := by
  rw [zeroIsoBase,Iso.trans_hom,FreeTwoSplitHyperplane.zeroIsoBase_hom,← Category.assoc]
  exact congrArg (· ≫ projectiveBundleProjection X)
    (LagrangianMatrixChart.eqToIso_subscheme_ι _ _ (zeroIdeal_eq_hyperplane X F j r hret t i))

include r hret in
theorem projection_isIso :
    IsIso ((zeroIdeal X F j t i).subschemeι ≫ projectiveBundleProjection X) := by
  rw [← zeroIsoBase_hom X F j r hret t i]
  infer_instance

end M9Native.SplitPairTensorZero

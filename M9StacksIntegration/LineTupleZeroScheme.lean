module

public import M9StacksIntegration.TensorFreeCoordinates
public import M9StacksIntegration.LineSectionIdealSum
public import M9StacksIntegration.ChowFreeLineTensor
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-!
# The full simultaneous zero ideal of a genuine line-section tuple

The tuple is an actual section of the line tensored with the original
finite free sheaf. Its actual coordinate projections recover the input
sections. Naturality on every test scheme identifies its native
dual-evaluation zero ideal with the sum of the original line zero ideals.
No radical, reduced structure, or regular prefix is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern
open MonoidalCategory

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf

universe u
namespace M9Native.LineTupleZeroScheme

open ChowCapWords GradedLineCapSubring TensorFreeCoordinates
open LinearIncidenceTensorCoordinates LagrangianMatrixChart

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

variable {X : Scheme.{u}} (L : InvertibleLine X) (n : ℕ)

local instance lineInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L.1 := L.2

/-- The actual rank-n bundle of n copies of the original line. -/
abbrev tupleBundle : X.Modules := tensorObj X L.1 (freeOn X n)

/-- The native symmetry compares the two actual tensor orientations. -/
def freeTensorIso : tupleBundle L n ≅ ChowFreeLineTensor.freeTensor L n := β_ _ _

instance tupleRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tupleBundle L n) n := by
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L.1 := L.2
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (ChowFreeBundleChern.freeBundle X n) n :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) n
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (freeTensorIso L n).symm
    (isFiniteLocallyFreeOfRank_sheafTensor (ChowFreeBundleChern.freeBundle X n) n L.1)

/-- The actual global section with the prescribed original line components. -/
def tupleSection (s : Fin n → Γ(L.1, ⊤)) : Γ(tupleBundle L n, ⊤) :=
  ∑ i : Fin n, (inclusion X L.1 n (ULift.up i)).app ⊤ (s i)

theorem inclusion_projection (i j : Fin n) :
    inclusion X L.1 n (ULift.up j) ≫ projection X L.1 n (ULift.up i) =
      if j=i then 𝟙 L.1 else 0 := by
  classical
  let T := tensorFunctor X L.1
  let _ := tensorFunctor_additive X L.1
  by_cases h : j=i
  · subst j
    simp only [TensorFreeCoordinates.inclusion, projection, Category.assoc, ← Functor.map_comp_assoc,
      SheafOfModules.ιFree_comp_freeProjection_self, ite_true]
    change (rightUnit X L.1).inv ≫ T.map (𝟙 _) ≫ (rightUnit X L.1).hom = _
    rw [T.map_id, Category.id_comp, Iso.inv_hom_id]
  · have h' : (ULift.up j : ULift.{u} (Fin n)) ≠ ULift.up i := by simpa
    simp only [TensorFreeCoordinates.inclusion, projection, Category.assoc, ← Functor.map_comp_assoc,
      SheafOfModules.ιFree_comp_freeProjection_of_ne h', Functor.map_zero,
      zero_comp, comp_zero, ite_eq_right h]

/-- Every literal coordinate projection recovers its original section. -/
theorem projection_tupleSection (s : Fin n → Γ(L.1, ⊤)) (i : Fin n) :
    (projection X L.1 n (ULift.up i)).app ⊤ (tupleSection L n s) = s i := by
  classical
  rw [tupleSection, map_sum]
  have h (j : Fin n) :
      (projection X L.1 n (ULift.up i)).app ⊤
        ((inclusion X L.1 n (ULift.up j)).app ⊤ (s j)) =
      if j=i then s j else 0 := by
    change (inclusion X L.1 n (ULift.up j) ≫
      projection X L.1 n (ULift.up i)).app ⊤ (s j) = _
    rw [inclusion_projection]
    split_ifs <;> simp
  simp_rw [h]
  simp

/-- On arbitrary test schemes, the actual tuple vanishes precisely when
all of its original line sections vanish. -/
theorem pullback_tupleSection_zero_iff (s : Fin n → Γ(L.1, ⊤))
    {T : Scheme.{u}} (p : T ⟶ X) :
    pullbackGlobalSections p (tupleBundle L n) (tupleSection L n s) = 0 ↔
      ∀ i, pullbackGlobalSections p L.1 (s i) = 0 := by
  constructor
  · intro h i
    rw [← projection_tupleSection L n s i,
      Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality, h, map_zero]
  · intro h
    rw [tupleSection, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality, h i, map_zero]

/-- The native rank-n dual-evaluation ideal is exactly the full sum of
the original line-section ideals. -/
theorem zeroIdeal_eq (s : Fin n → Γ(L.1, ⊤)) :
    zeroSchemeOfSection X (tupleBundle L n) (tupleSection L n s) =
      LineSectionIdealSum.ideal L.1 (List.ofFn s) := by
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L.1 := L.2
  have hf {T : Scheme.{u}} (p : T ⟶ X) :
      (∃ g : T ⟶ (zeroSchemeOfSection X (tupleBundle L n) (tupleSection L n s)).subscheme,
        g ≫ (zeroSchemeOfSection X (tupleBundle L n) (tupleSection L n s)).subschemeι = p) ↔
      ∃ g : T ⟶ (LineSectionIdealSum.ideal L.1 (List.ofFn s)).subscheme,
        g ≫ (LineSectionIdealSum.ideal L.1 (List.ofFn s)).subschemeι = p := by
    have hline : (∀ i, pullbackGlobalSections p L.1 (s i) = 0) ↔
        ∃ g : T ⟶ (LineSectionIdealSum.ideal L.1 (List.ofFn s)).subscheme,
          g ≫ (LineSectionIdealSum.ideal L.1 (List.ofFn s)).subschemeι = p := by
      rw [LineSectionIdealSum.ideal_factors_iff]
      constructor
      · intro h z hz
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
        exact h i
      · intro h i
        exact h (s i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
      (tupleBundle L n) n (tupleSection L n s) p).symm.trans
      ((pullback_tupleSection_zero_iff L n s p).trans hline)
  apply le_antisymm
  · have h := (hf (LineSectionIdealSum.ideal L.1 (List.ofFn s)).subschemeι).mpr
      ⟨𝟙 _, by simp⟩
    exact (factorsThrough_ideal_iff_ideal_le_ker _ _).mp h |>.trans_eq
      (Scheme.IdealSheafData.ker_subschemeι _)
  · have h := (hf (zeroSchemeOfSection X (tupleBundle L n) (tupleSection L n s)).subschemeι).mp
      ⟨𝟙 _, by simp⟩
    exact (factorsThrough_ideal_iff_ideal_le_ker _ _).mp h |>.trans_eq
      (Scheme.IdealSheafData.ker_subschemeι _)

/-- Native Whitney for the genuine free line twist computes the full
total Chern family of the actual tuple bundle. -/
theorem chernFamily_tupleBundle (C : ChowSituation.{u}) (q : X ⟶ C.S)
    [LocallyOfFiniteType q] :
    chernFamily C q (tupleBundle L n) n = (1 + lineFamily C q L)^n :=
  ChowFreeLineTensor.chernFamily_of_iso_freeTensor C q (tupleBundle L n) L n (freeTensorIso L n)

end M9Native.LineTupleZeroScheme

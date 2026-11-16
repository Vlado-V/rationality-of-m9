module

public import M9StacksIntegration.SectionZeroSubbundle
public import M9StacksIntegration.IteratedLineSectionCuts
public import M9StacksIntegration.LagrangianMatrixChart

/-! Full closed intersections are compared by their actual all-test
pullback universal property. No supports, radicals, or field-point
replacement occurs in these comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.IdealIntersectionPullback
open IteratedLineSectionCuts
variable {X Y : Scheme.{u}}

theorem factors_closedMap_iff_kernel (l : Y ⟶ X) [IsClosedImmersion l]
    {T : Scheme.{u}} (f : T ⟶ X) :
    (∃ a : T ⟶ Y, a ≫ l = f) ↔ l.ker ≤ f.ker := by
  constructor
  · rintro ⟨a, rfl⟩
    exact Scheme.Hom.le_ker_comp a l
  · intro h
    obtain ⟨b, hb⟩ := (factorsThrough_ideal_iff_ideal_le_ker l.ker f).mpr h
    refine ⟨b ≫ (asIso l.toImage).inv, ?_⟩
    rw [Category.assoc, LagrangianMatrixChart.asIso_toImage_inv_imageι]
    exact hb

theorem comap_factors_comp_iff (l : Y ⟶ X) (I : X.IdealSheafData)
    {T : Scheme.{u}} (f : T ⟶ X) :
    (∃ a : T ⟶ (I.comap l).subscheme,
      a ≫ ((I.comap l).subschemeι ≫ l) = f) ↔
      (∃ a : T ⟶ Y, a ≫ l = f) ∧
        ∃ b : T ⟶ I.subscheme, b ≫ I.subschemeι = f := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨⟨a ≫ (I.comap l).subschemeι, by simpa only [Category.assoc] using ha⟩,
      ⟨a ≫ (I.comapIso l).hom ≫ pullback.snd _ _, ?_⟩⟩
    rw [Category.assoc, Category.assoc, ← pullback.condition,
      ← Category.assoc (I.comapIso l).hom,
      Scheme.IdealSheafData.comapIso_hom_fst]
    exact ha
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨pullback.lift a b (ha.trans hb.symm) ≫ (I.comapIso l).inv, ?_⟩
    rw [Category.assoc, ← Category.assoc (I.comapIso l).inv,
      Scheme.IdealSheafData.comapIso_inv_subschemeι, pullback.lift_fst_assoc, ha]

theorem closedComap_factors_sup_iff (l : Y ⟶ X) [IsClosedImmersion l]
    (I : X.IdealSheafData) {T : Scheme.{u}} (f : T ⟶ X) :
    (∃ a : T ⟶ (I.comap l).subscheme,
      a ≫ ((I.comap l).subschemeι ≫ l) = f) ↔
      ∃ b : T ⟶ (l.ker ⊔ I).subscheme, b ≫ (l.ker ⊔ I).subschemeι = f := by
  rw [comap_factors_comp_iff, factors_closedMap_iff_kernel,
    factorsThrough_ideal_iff_ideal_le_ker, factorsThrough_ideal_iff_ideal_le_ker,
    sup_le_iff]

/-- The true closed Cartesian pullback is the full ideal-sum intersection. -/
def closedComapIsoSup (l : Y ⟶ X) [IsClosedImmersion l] (I : X.IdealSheafData) :
    (I.comap l).subscheme ≅ (l.ker ⊔ I).subscheme := by
  let : Mono (Over.mk ((I.comap l).subschemeι ≫ l)).hom := by
    change Mono ((I.comap l).subschemeι ≫ l)
    infer_instance
  let : Mono (Over.mk (l.ker ⊔ I).subschemeι).hom := by
    change Mono (l.ker ⊔ I).subschemeι
    infer_instance
  exact comparisonIso (Over.mk ((I.comap l).subschemeι ≫ l))
    (Over.mk (l.ker ⊔ I).subschemeι) (fun _ f => closedComap_factors_sup_iff l I f)

@[reassoc]
theorem closedComapIsoSup_hom_comp (l : Y ⟶ X) [IsClosedImmersion l]
    (I : X.IdealSheafData) :
    (closedComapIsoSup l I).hom ≫ (l.ker ⊔ I).subschemeι =
      (I.comap l).subschemeι ≫ l := by
  let : Mono (Over.mk ((I.comap l).subschemeι ≫ l)).hom := by
    change Mono ((I.comap l).subschemeι ≫ l)
    infer_instance
  let : Mono (Over.mk (l.ker ⊔ I).subschemeι).hom := by
    change Mono (l.ker ⊔ I).subschemeι
    infer_instance
  exact comparisonIso_hom_comp (Over.mk ((I.comap l).subschemeι ≫ l))
    (Over.mk (l.ker ⊔ I).subschemeι) (fun _ f => closedComap_factors_sup_iff l I f)

end M9Native.IdealIntersectionPullback

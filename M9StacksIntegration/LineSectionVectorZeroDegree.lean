module

public import M9StacksIntegration.CurveSectionZeroChowDegree
public import M9StacksIntegration.FiniteClosedSectionH0
public import M9StacksIntegration.NonzeroSectionZeroFinite
public import M9StacksIntegration.SectionZeroSubbundle

/-! A genuine section of a line mapping into a vector bundle vanishes on
a closed subscheme of the full vector-section zero. Its actual line degree
is therefore bounded by the original-field structural H0 of that full zero.
Neither a divisor inclusion nor a length inequality is supplied. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.Chow
universe u

namespace M9Native.LineSectionVectorZeroDegree

variable {X : Scheme.{u}}

/-- Any actual module map gives containment of the full zero ideals,
without an injectivity or reducedness assumption on that map. -/
theorem zeroIdeal_image_le (E F : X.Modules) (r q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F q]
    (j : E ⟶ F) (s : Γ(E, ⊤)) :
    zeroSchemeOfSection X F (j.app ⊤ s) ≤ zeroSchemeOfSection X E s := by
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F q
  rw [NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal,
    NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal]
  let I := SectionZeroIdealFactorization.sectionZeroIdeal X E s
  have hs : pullbackGlobalSections I.subschemeι E s = 0 :=
    (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
      E r s I.subschemeι).mpr ⟨𝟙 _, by simp only [Category.id_comp]; rfl⟩
  have hj : pullbackGlobalSections I.subschemeι F (j.app ⊤ s) = 0 := by
    rw [← SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections, hs, map_zero]
  have hf := (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    F q (j.app ⊤ s) I.subschemeι).mp hj
  rw [factorsThrough_ideal_iff_ideal_le_ker, Scheme.IdealSheafData.ker_subschemeι] at hf
  exact hf

variable (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f]

/-- The native closed inclusion gives the genuine H0 inequality,
with all nilpotents and the original structural field action retained. -/
theorem zero_H0_le (E F : X.Modules) (r q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F q]
    (j : E ⟶ F) (s : Γ(E, ⊤)) (hs : j.app ⊤ s ≠ 0) :
    finrank K (structureSheafCohomology ((zeroSchemeOfSection X E s).subschemeι ≫ f) 0) ≤
      finrank K (structureSheafCohomology
        ((zeroSchemeOfSection X F (j.app ⊤ s)).subschemeι ≫ f) 0) := by
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F q
  letI : IsFinite ((zeroSchemeOfSection X F (j.app ⊤ s)).subschemeι ≫ f) :=
    NonzeroSectionZeroFinite.isFinite_zeroSchemeOfSection_of_isCurve F (j.app ⊤ s) K f hs
  exact FiniteClosedSectionH0.h0_le_of_ideal_le K f _ _ (zeroIdeal_image_le E F r q j s)

/-- The actual degree of the line is bounded by the structural H0 of
the full vector zero scheme; its Cartier divisor and finiteness are derived. -/
theorem line_degree_le_zero_H0 (L F : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F q]
    (j : L ⟶ F) (s : Γ(L, ⊤)) (hs : s ≠ 0) (hj : j.app ⊤ s ≠ 0) :
    invertibleCurveDegree K f (IsCurve.topologicalKrullDim_eq_one f).le L ≤
      (finrank K (structureSheafCohomology
        ((zeroSchemeOfSection X F (j.app ⊤ s)).subschemeι ≫ f) 0) : ℤ) := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  have hb := zero_H0_le K f L F 1 q j s hj
  let D := zeroSchemeOfSection X L s
  letI : Algebra K Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have hd := invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one
    K f (IsCurve.topologicalKrullDim_eq_one f).le L
    (CurveSectionZeroChowDegree.nativeSection L s)
    (by simpa only [CurveSectionZeroChowDegree.nativeSection_eval] using hs)
    D (CurveSectionZeroChowDegree.nativeSection_zero_geometric L s)
  have hc := FiniteClosedSectionH0.structureH0_finrank_eq_functions K (D.subschemeι ≫ f)
  have hdeg : invertibleCurveDegree K f (IsCurve.topologicalKrullDim_eq_one f).le L =
      (finrank K (structureSheafCohomology
        ((zeroSchemeOfSection X L s).subschemeι ≫ f) 0) : ℤ) := by
    exact hd.trans (congrArg (fun n : ℕ => (n : ℤ)) hc.symm)
  rw [hdeg]
  exact_mod_cast hb

end M9Native.LineSectionVectorZeroDegree

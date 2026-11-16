module

public import M9StacksIntegration.LineSectionIdealSum
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible row changes of actual sections of the same line

The coefficients act through the original ring homomorphism to global
functions. The inverse matrix recovers the original tuple. Canonical
pullback transports this action on every test scheme; hence the actual
sum zero ideals agree and their native zero schemes, as well as their
successive-cut models, are isomorphic over the original ambient scheme.
The nilpotent structures are retained by the all-test universal property.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
open scoped BigOperators

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u v w

namespace M9Native.LineSectionRowChange

section Modules

variable {K : Type u} [CommRing K] {R : Type v} [CommRing R]
  {M : Type w} [AddCommGroup M] [Module R M] {n : ℕ}

/-- The literal row action through the original coefficient map. -/
def rowChange (ρ : K →+* R) (A : GL (Fin n) K) (s : Fin n → M) : Fin n → M :=
  fun i => ∑ j : Fin n, ρ (A.val i j) • s j

theorem rowChange_mul (ρ : K →+* R) (A B : GL (Fin n) K) (s : Fin n → M) :
    rowChange ρ A (rowChange ρ B s) = rowChange ρ (A * B) s := by
  funext i
  change (∑ j : Fin n, ρ (A.val i j) • (∑ k : Fin n, ρ (B.val j k) • s k)) =
    ∑ k : Fin n, ρ ((A.val * B.val) i k) • s k
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply, map_sum, map_mul]

theorem rowChange_one (ρ : K →+* R) (s : Fin n → M) : rowChange ρ 1 s = s := by
  funext i
  simp [rowChange, Matrix.one_apply]

/-- The genuine inverse equation matrix recovers the entire original tuple. -/
theorem rowChange_inverse (ρ : K →+* R) (A : GL (Fin n) K) (s : Fin n → M) :
    rowChange ρ A⁻¹ (rowChange ρ A s) = s := by
  rw [rowChange_mul, inv_mul_cancel, rowChange_one]

theorem rowChange_all_zero_iff (ρ : K →+* R) (A : GL (Fin n) K) (s : Fin n → M) :
    (∀ j, s j = 0) ↔ ∀ i, rowChange ρ A s i = 0 := by
  constructor
  · intro h i
    simp only [rowChange, h, smul_zero, Finset.sum_const_zero]
  · intro h i
    have hi := congrFun (rowChange_inverse ρ A s) i
    have hz : rowChange ρ A⁻¹ (rowChange ρ A s) i = 0 := by
      change (∑ j : Fin n, ρ ((A⁻¹).val i j) • rowChange ρ A s j) = 0
      simp only [h, smul_zero, Finset.sum_const_zero]
    exact hi.symm.trans hz

end Modules

section Schemes

variable {K : Type u} [CommRing K] {X : Scheme.{u}} {n : ℕ}
  (ρ : K →+* Γ(X, ⊤)) (L : X.Modules) (A : GL (Fin n) K) (s : Fin n → Γ(L, ⊤))

/-- Canonical pullback transports every original row coefficient and
section, on any actual test scheme. -/
theorem pullback_rowChange {T : Scheme.{u}} (p : T ⟶ X) (i : Fin n) :
    pullbackGlobalSections p L (rowChange ρ A s i) =
      rowChange (p.appTop.hom.comp ρ) A (fun j => pullbackGlobalSections p L (s j)) i := by
  simp only [rowChange, map_sum, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    RingHom.comp_apply]

/-- Simultaneous vanishing is invariant on every test scheme; its
inverse direction is derived from the actual inverse matrix. -/
theorem pullback_all_zero_iff {T : Scheme.{u}} (p : T ⟶ X) :
    (∀ j, pullbackGlobalSections p L (s j) = 0) ↔
      ∀ i, pullbackGlobalSections p L (rowChange ρ A s i) = 0 := by
  simp_rw [pullback_rowChange]
  exact rowChange_all_zero_iff (p.appTop.hom.comp ρ) A (fun j => pullbackGlobalSections p L (s j))

variable [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The full sum of the actual native section zero ideals. -/
abbrev tupleIdeal (t : Fin n → Γ(L, ⊤)) : X.IdealSheafData :=
  LineSectionIdealSum.ideal L (List.ofFn t)

theorem tupleIdeal_factors_iff (t : Fin n → Γ(L, ⊤)) {T : Scheme.{u}} (p : T ⟶ X) :
    (∃ g : T ⟶ (tupleIdeal L t).subscheme, g ≫ (tupleIdeal L t).subschemeι = p) ↔
      ∀ i, pullbackGlobalSections p L (t i) = 0 := by
  rw [LineSectionIdealSum.ideal_factors_iff]
  constructor
  · intro h i
    exact h (t i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact h i

theorem factors_rowChange_iff {T : Scheme.{u}} (p : T ⟶ X) :
    (∃ g : T ⟶ (tupleIdeal L s).subscheme, g ≫ (tupleIdeal L s).subschemeι = p) ↔
      ∃ g : T ⟶ (tupleIdeal L (rowChange ρ A s)).subscheme,
        g ≫ (tupleIdeal L (rowChange ρ A s)).subschemeι = p :=
  (tupleIdeal_factors_iff L s p).trans ((pullback_all_zero_iff ρ L A s p).trans
    (tupleIdeal_factors_iff L (rowChange ρ A s) p).symm)

/-- Equality of the full actual ideal sheaves, including their nilpotents. -/
theorem tupleIdeal_eq : tupleIdeal L s = tupleIdeal L (rowChange ρ A s) := by
  apply le_antisymm
  · have hf := (factors_rowChange_iff ρ L A s
      (tupleIdeal L (rowChange ρ A s)).subschemeι).mpr ⟨𝟙 _, by simp⟩
    have hle := (factorsThrough_ideal_iff_ideal_le_ker (tupleIdeal L s)
      (tupleIdeal L (rowChange ρ A s)).subschemeι).mp hf
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hle
  · have hf := (factors_rowChange_iff ρ L A s (tupleIdeal L s).subschemeι).mp
      ⟨𝟙 _, by simp⟩
    have hle := (factorsThrough_ideal_iff_ideal_le_ker (tupleIdeal L (rowChange ρ A s))
      (tupleIdeal L s).subschemeι).mp hf
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hle

/-- The genuine native sum-zero-scheme isomorphism, constructed from
the proved factorization law on all test schemes. -/
def zeroSchemeIso : (tupleIdeal L s).subscheme ≅ (tupleIdeal L (rowChange ρ A s)).subscheme := by
  let : Mono (Over.mk (tupleIdeal L s).subschemeι).hom := by
    change Mono (tupleIdeal L s).subschemeι
    infer_instance
  let : Mono (Over.mk (tupleIdeal L (rowChange ρ A s)).subschemeι).hom := by
    change Mono (tupleIdeal L (rowChange ρ A s)).subschemeι
    infer_instance
  exact IteratedLineSectionCuts.comparisonIso (Over.mk (tupleIdeal L s).subschemeι)
    (Over.mk (tupleIdeal L (rowChange ρ A s)).subschemeι)
    (fun _ p => factors_rowChange_iff ρ L A s p)

@[reassoc]
theorem zeroSchemeIso_hom_comp :
    (zeroSchemeIso ρ L A s).hom ≫ (tupleIdeal L (rowChange ρ A s)).subschemeι =
      (tupleIdeal L s).subschemeι := by
  let : Mono (Over.mk (tupleIdeal L s).subschemeι).hom := by
    change Mono (tupleIdeal L s).subschemeι
    infer_instance
  let : Mono (Over.mk (tupleIdeal L (rowChange ρ A s)).subschemeι).hom := by
    change Mono (tupleIdeal L (rowChange ρ A s)).subschemeι
    infer_instance
  exact IteratedLineSectionCuts.comparisonIso_hom_comp
    (Over.mk (tupleIdeal L s).subschemeι)
    (Over.mk (tupleIdeal L (rowChange ρ A s)).subschemeι)
    (fun _ p => factors_rowChange_iff ρ L A s p)

@[reassoc]
theorem zeroSchemeIso_inv_comp :
    (zeroSchemeIso ρ L A s).inv ≫ (tupleIdeal L s).subschemeι =
      (tupleIdeal L (rowChange ρ A s)).subschemeι := by
  let : Mono (Over.mk (tupleIdeal L s).subschemeι).hom := by
    change Mono (tupleIdeal L s).subschemeι
    infer_instance
  let : Mono (Over.mk (tupleIdeal L (rowChange ρ A s)).subschemeι).hom := by
    change Mono (tupleIdeal L (rowChange ρ A s)).subschemeι
    infer_instance
  exact IteratedLineSectionCuts.comparisonIso_inv_comp
    (Over.mk (tupleIdeal L s).subschemeι)
    (Over.mk (tupleIdeal L (rowChange ρ A s)).subschemeι)
    (fun _ p => factors_rowChange_iff ρ L A s p)

/-- Actual successive-cut models are likewise isomorphic over the
original ambient scheme, by their genuine native sum-ideal comparison. -/
def cutIso : (IteratedLineSectionCuts.simultaneousCut L (List.ofFn s)).left ≅
    (IteratedLineSectionCuts.simultaneousCut L (List.ofFn (rowChange ρ A s))).left :=
  LineSectionIdealSum.cutIso L (List.ofFn s) ≪≫ zeroSchemeIso ρ L A s ≪≫
    (LineSectionIdealSum.cutIso L (List.ofFn (rowChange ρ A s))).symm

@[reassoc]
theorem cutIso_hom_comp :
    (cutIso ρ L A s).hom ≫
      (IteratedLineSectionCuts.simultaneousCut L (List.ofFn (rowChange ρ A s))).hom =
        (IteratedLineSectionCuts.simultaneousCut L (List.ofFn s)).hom := by
  simp only [cutIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    LineSectionIdealSum.cutIso_inv_comp, zeroSchemeIso_hom_comp,
    LineSectionIdealSum.cutIso_hom_comp]

end Schemes

end M9Native.LineSectionRowChange

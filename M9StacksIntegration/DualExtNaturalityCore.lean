module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Naturality of actual Ext cancellation

The first lemma is the original map-of-Ext naturality square, with its
actual source and target comparisons. The rigid construction uses the
actual tensor-dual adjunction. It will be specialized to genuine sheaf
of modules duals; no replacement Ext group is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory

universe u v w

namespace M9Native.DualExtNaturalityCore

section ExactFunctors

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {F G : C ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Actual Ext functoriality with both cancellation comparisons retained. -/
theorem cancellation_naturality (τ : F ⟶ G) {A B Q O D E : C}
    (g : B ⟶ A) (u : O ⟶ F.obj A) (v : O ⟶ G.obj B)
    (s : F.obj Q ⟶ D) (t : G.obj Q ⟶ E) (a : D ⟶ E)
    (hu : u ≫ τ.app A = v ≫ G.map g) (hs : τ.app Q ≫ t = s ≫ a)
    (n : ℕ) (ξ : Ext A Q n) :
    ((Ext.mk₀ v).comp (((Ext.mk₀ g).comp ξ (zero_add n)).mapExactFunctor G)
      (zero_add n)).comp (Ext.mk₀ t) (add_zero n) =
    (((Ext.mk₀ u).comp (ξ.mapExactFunctor F) (zero_add n)).comp (Ext.mk₀ s)
      (add_zero n)).comp (Ext.mk₀ a) (add_zero n) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    ← hu, ← Ext.mk₀_comp_mk₀_assoc,
    ← Ext.mapExactFunctor_comp_mk₀_natTransApp ξ τ]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hs]

end ExactFunctors

section Rigid

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [MonoidalCategory C]

variable (L : C) [HasRightDual L]
  [(tensorRight L).Additive] [(tensorRight (Lᘁ)).Additive]
  [PreservesFiniteLimits (tensorRight L)] [PreservesFiniteColimits (tensorRight L)]
  [PreservesFiniteLimits (tensorRight (Lᘁ))] [PreservesFiniteColimits (tensorRight (Lᘁ))]

/-- Canonical actual Ext from an object is Ext from the unit into its
actual right dual, using the tensor-dual adjunction and native unitors. -/
def dualExtAddEquiv (n : ℕ) : Ext L (𝟙_ C) n ≃+ Ext (𝟙_ C) (Lᘁ) n :=
  ((((extFunctor n).mapIso (λ_ L).op).app (𝟙_ C)).addCommGroupIsoToAddEquiv).trans
    ((tensorRightAdjunction L (Lᘁ)).extEquiv.trans
      (((extFunctorObj (𝟙_ C) n).mapIso (λ_ (Lᘁ))).addCommGroupIsoToAddEquiv))

/-- On actual classes this cancellation is coevaluation, actual tensor
transport and the actual left unitor. -/
theorem dualExtAddEquiv_apply (n : ℕ) (ξ : Ext L (𝟙_ C) n) :
    dualExtAddEquiv L n ξ =
      ((Ext.mk₀ (η_ L (Lᘁ))).comp (ξ.mapExactFunctor (tensorRight (Lᘁ)))
        (zero_add n)).comp (Ext.mk₀ (λ_ (Lᘁ)).hom) (add_zero n) := by
  change ((tensorRightAdjunction L (Lᘁ)).extEquiv
    ((Ext.mk₀ (λ_ L).hom).comp ξ (zero_add n))).comp
      (Ext.mk₀ (λ_ (Lᘁ)).hom) (add_zero n) = _
  rw [Adjunction.extEquiv_naturality_right, Adjunction.extEquiv_mk₀]
  congr 2
  congr 1
  simp only [tensorRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  dsimp [tensorRightHomEquiv]
  monoidal

variable {L} (M : C) [HasRightDual M]
  [(tensorRight M).Additive] [(tensorRight (Mᘁ)).Additive]
  [PreservesFiniteLimits (tensorRight M)] [PreservesFiniteColimits (tensorRight M)]
  [PreservesFiniteLimits (tensorRight (Mᘁ))] [PreservesFiniteColimits (tensorRight (Mᘁ))]

/-- Precomposition in the first actual Ext argument is the dual mate on
its actual coefficient object, in every degree. -/
theorem dualExtAddEquiv_naturality (φ : L ⟶ M) (n : ℕ)
    (ξ : Ext M (𝟙_ C) n) :
    dualExtAddEquiv L n ((Ext.mk₀ φ).comp ξ (zero_add n)) =
      (dualExtAddEquiv M n ξ).comp (Ext.mk₀ (rightAdjointMate φ)) (add_zero n) := by
  rw [dualExtAddEquiv_apply, dualExtAddEquiv_apply]
  exact cancellation_naturality
    ((tensoringRight C).map (rightAdjointMate φ)) φ
    (η_ M (Mᘁ)) (η_ L (Lᘁ)) (λ_ (Mᘁ)).hom (λ_ (Lᘁ)).hom
    (rightAdjointMate φ)
    (coevaluation_comp_rightAdjointMate φ)
    (leftUnitor_naturality (rightAdjointMate φ)) n ξ

end Rigid

end M9Native.DualExtNaturalityCore

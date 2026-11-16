module

public import M9StacksIntegration.ChowSplitLineProjectiveZero
public import M9StacksIntegration.ChowHyperplanePieces
public import M9StacksIntegration.RankTwoSelectedPairSheafEntries

/-! A literal unimodular row on the ORIGINAL free-two projective
bundle cuts out a scheme isomorphic to the original base. Both
original coordinate positions and the exact tautological sections are
retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeProj
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.Scheme.unitModule
  SheafOfModules.unit PresheafOfModules.unit
namespace M9Native.FreeTwoSplitHyperplane

open LagrangianMatrixChart FreeTwoCoordinates

variable (X : Scheme.{u}) (t : Scheme.unitModule X ⟶ Scheme.unitModule X) (i : Fin 2)

def subline : Scheme.unitModule X ⟶ freeOn X 2 :=
  FreeTwoCoordinates.inclusion X i + t ≫ FreeTwoCoordinates.inclusion X (other i)

def quotient : freeOn X 2 ⟶ Scheme.unitModule X :=
  FreeTwoCoordinates.projection X (other i) - FreeTwoCoordinates.projection X i ≫ t

@[reassoc]
theorem section_quotient : FreeTwoCoordinates.inclusion X (other i) ≫ quotient X t i =
    𝟙 (Scheme.unitModule X) := by
  simp only [quotient, Preadditive.comp_sub, ← Category.assoc, inclusion_projection_self]
  rw [inclusion_projection, ite_eq_right (other_ne_self i), zero_comp, sub_zero]

instance quotient_isSplitEpi : IsSplitEpi (quotient X t i) :=
  ⟨⟨FreeTwoCoordinates.inclusion X (other i), section_quotient X t i⟩⟩

/-- The actual four maps satisfy the split identities by the original
free-coordinate Kronecker relations. No splitting is assumed. -/
def splitting : UnitSplitting (quotient X t i) where
  σ := subline X t i
  τ := FreeTwoCoordinates.projection X i
  σ' := FreeTwoCoordinates.inclusion X (other i)
  hsplit := by
    simp only [subline, quotient, Preadditive.comp_add, Preadditive.sub_comp, Category.assoc]
    calc
      _ = FreeTwoCoordinates.projection X i ≫ FreeTwoCoordinates.inclusion X i +
          FreeTwoCoordinates.projection X (other i) ≫
            FreeTwoCoordinates.inclusion X (other i) := by abel
      _ = _ := splitting_identity X i
  hσu := by
    simp [subline, quotient, Preadditive.add_comp, Preadditive.comp_sub,
      Category.assoc, inclusion_projection, inclusion_projection_assoc,
      Ne.symm (other_ne_self i)]
  hστ := by
    simp [subline, Preadditive.add_comp, Category.assoc, inclusion_projection]
  hσ'τ := by rw [inclusion_projection, ite_eq_right (other_ne_self i)]
  hσ'u := section_quotient X t i

theorem subline_section : (subline X t i).app ⊤ (1 : Γ(X,⊤)) =
    freeBasisSection X 2 i + (Stacks.FreeSheafMatrix.unitEndValue t) •
      freeBasisSection X 2 (other i) := by
  change (FreeTwoCoordinates.inclusion X i).app ⊤ (1 : Γ(X,⊤)) +
    (FreeTwoCoordinates.inclusion X (other i)).app ⊤ (t.app ⊤ (1 : Γ(X,⊤))) = _
  have h : t.app ⊤ (1 : Γ(X,⊤)) =
      (Stacks.FreeSheafMatrix.unitEndValue t) • (1 : Γ(X,⊤)) := by
    change (Stacks.FreeSheafMatrix.unitEndValue t) =
      (Stacks.FreeSheafMatrix.unitEndValue t) * 1
    exact (mul_one _).symm
  rw [h, Scheme.Modules.Hom.app_smul]
  rfl

/-- The actual original tautological quotient applied to the actual
split unit subline. -/
abbrev originalSection := ChowHyperplanePieces.originalSection (freeOn X 2)
  (Stacks.Chow.bundlePieces (freeOn X 2)) (subline X t i)

theorem unit_invertible : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
    (Scheme.unitModule X) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (Stacks.SheafOfModules.isInvertible_unit _ _)

abbrev zeroIdeal := ChowHyperplanePieces.zeroIdeal (freeOn X 2)
  (Stacks.Chow.bundlePieces (freeOn X 2)) (subline X t i)

def zeroIsoBase : (zeroIdeal X t i).subscheme ≅ X :=
  ChowHyperplanePieces.zeroIsoBase (quotient X t i) (splitting X t i)
    (unit_invertible X) (Stacks.Chow.bundlePieces (freeOn X 2))

theorem zeroIsoBase_hom : (zeroIsoBase X t i).hom =
    (zeroIdeal X t i).subschemeι ≫ Stacks.Chow.bundleProj (freeOn X 2) :=
  ChowHyperplanePieces.zeroIsoBase_hom (quotient X t i) (splitting X t i)
    (unit_invertible X) (Stacks.Chow.bundlePieces (freeOn X 2))

instance zeroProjection_isIso :
    IsIso ((zeroIdeal X t i).subschemeι ≫ Stacks.Chow.bundleProj (freeOn X 2)) := by
  rw [← zeroIsoBase_hom]
  infer_instance

end M9Native.FreeTwoSplitHyperplane

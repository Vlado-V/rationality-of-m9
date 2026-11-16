module

public import M9StacksIntegration.MukaiBundle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerArbitraryIndex
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation

/-!
# Tensor cancellation and the actual free top exterior power

These helpers use the native sheaf tensor, its actual evaluation pairing,
and the actual exterior basis of a free sheaf. In particular the residual
relation for the literal sheaf `ω ⊗ αᵛ` is constructed, and its invertibility
is derived when ω and α are invertible. No residual isomorphism or
vector-bundle determinant identity is an input.

The public namespace is `M9Native.MukaiBundleDeterminant`, shared with
`MukaiBundleDeterminant.lean`, which applies these helpers to the actual
short exact sequences. This leaf has only the already compiled imports;
verification is recorded separately in its audit receipt.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle

universe u

namespace M9Native.MukaiBundleDeterminant

variable {X : Scheme.{u}}

/-- The actual tensor product of sheaves on the native scheme. -/
abbrev tensor (A B : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj B

/-- The actual top exterior power, with its rank displayed. -/
abbrev topExterior (F : X.Modules) (r : ℕ) : X.Modules :=
  Scheme.Modules.exteriorPower F (r : ℤ)

/-- Functoriality of the actual tensor in both arguments. -/
def tensorIso {A A' B B' : X.Modules} (e : A ≅ A') (e' : B ≅ B') :
    tensor A B ≅ tensor A' B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).mapIso e).app B ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A').mapIso e'

/-- Comparison with the normalized sheaf-of-rings proof used by the
native inverse uniqueness theorem. -/
def tensorToNormalizedIso (A B : X.Modules) :
    tensor A B ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).obj B :=
  Iso.refl _

/-- An actual tensor inverse is the actual native sheaf dual. -/
def tensorInverseNativeIso (L N : X.Modules) (e : tensor L N ≅ structureModule X) :
    N ≅ dualSheaf L :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf X.ringCatSheaf.2
    L N ((tensorToNormalizedIso L N).symm ≪≫ e)

/-- The literal residual sheaf `ω ⊗ αᵛ`. -/
abbrev residualLine (ω α : X.Modules) : X.Modules := tensor ω (dualSheaf α)

/-- The actual residual tensor relation, constructed from associativity,
symmetry, and the actual evaluation pairing of the invertible α. -/
def residualTensorIso (ω α : X.Modules)
    [hα : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α] :
    tensor α (residualLine ω α) ≅ ω := by
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property α :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ α hα
  let eα : tensor (dualSheaf α) α ≅ structureModule X :=
    Stacks.SheafOfModules.Scheme.evaluationIso X α
  exact
    (Stacks.SheafOfModules.Invertible.tensorProductAssociator X.presheaf X.ringCatSheaf.2
      α ω (dualSheaf α)).symm ≪≫
    tensorIso
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2 α ω)
      (Iso.refl _) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductAssociator X.presheaf X.ringCatSheaf.2
      ω α (dualSheaf α) ≪≫
    tensorIso (Iso.refl ω)
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
        α (dualSheaf α) ≪≫ eα) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 ω

/-- The literal residual sheaf of two invertible sheaves is invertible. -/
theorem residualLine_isInvertible (ω α : X.Modules)
    [hω : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω]
    [hα : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (residualLine ω α) := by
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ ω hω
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ α hα
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (dualSheaf α) :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf X.ringCatSheaf.2 α
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2
      ω (dualSheaf α))

/-- There is exactly one full-cardinality subset of the standard basis. -/
def fullSubsetEquiv (r : ℕ) :
    ↥(Set.powersetCard (ULift.{u} (Fin r)) r) ≃ PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨Finset.univ, by simp [Set.powersetCard]⟩
  left_inv s := by
    apply Subtype.ext
    exact (Finset.eq_univ_of_card s.val (by simp)).symm
  right_inv _ := rfl

/-- The top exterior power of an actual free sheaf is the structure
sheaf, computed by its exterior basis rather than a determinant premise. -/
def freeTopExteriorIso (r : ℕ) (F : X.Modules)
    (e : F ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) :
    topExterior F r ≅ structureModule X :=
  Stacks.SheafOfModules.exteriorPowerFreeIsoOfIsoAnyIndex
      (_root_.Opens.grothendieckTopology X) (ULift.{u} (Fin r)) r
      (SheafOfModules.algebras _ F) e ≪≫
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso (fullSubsetEquiv r).toIso ≪≫
      coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)

end M9Native.MukaiBundleDeterminant

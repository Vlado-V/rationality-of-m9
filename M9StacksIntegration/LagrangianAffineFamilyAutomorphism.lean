module

public import M9StacksIntegration.LagrangianSymplecticFamilyAutomorphism
public import Mathlib.AlgebraicGeometry.AffineSpace

/-! Actual variable symplectic automorphisms on native affine space
over LG. The native affine-space base-change square supplies the product
comparison, and the proved family automorphism is conjugated through it.
All affine parameters and the original ground-field map are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
universe u

namespace M9Native.LagrangianAffineFamilyAutomorphism

open LagrangianGrassmannian LagrangianTransitivity LagrangianVariableSymplecticAction
variable (K : Type u) [Field K] (n : Type u)

abbrev affineBase : Scheme.{u} := 𝔸(n;Spec (.of K))
abbrev affineLG : Scheme.{u} := 𝔸(n;space K)
abbrev baseProjection : affineBase K n ⟶ Spec (.of K) := affineBase K n ↘ Spec (.of K)
abbrev lgProjection : affineLG K n ⟶ space K := affineLG K n ↘ space K
abbrev parameterMap : affineLG K n ⟶ affineBase K n := AffineSpace.map n (projection K)

/-- The genuine native affine-space base-change isomorphism. -/
def comparison : affineLG K n ≅
    LagrangianSymplecticFamilyAutomorphism.family K (baseProjection K n) :=
  (AffineSpace.isPullback_map (n:=n) (projection K)).flip.isoPullback

@[reassoc] theorem comparison_toLG :
    (comparison K n).hom ≫
      LagrangianSymplecticFamilyAutomorphism.toLG K (baseProjection K n) = lgProjection K n :=
  (AffineSpace.isPullback_map (n:=n) (projection K)).flip.isoPullback_hom_fst

@[reassoc] theorem comparison_toBase :
    (comparison K n).hom ≫
      LagrangianSymplecticFamilyAutomorphism.toBase K (baseProjection K n) = parameterMap K n :=
  (AffineSpace.isPullback_map (n:=n) (projection K)).flip.isoPullback_hom_snd

@[reassoc] theorem comparison_inv_toLG :
    (comparison K n).inv ≫ lgProjection K n =
      LagrangianSymplecticFamilyAutomorphism.toLG K (baseProjection K n) := by
  rw [← comparison_toLG, Iso.inv_hom_id_assoc]

@[reassoc] theorem comparison_inv_toBase :
    (comparison K n).inv ≫ parameterMap K n =
      LagrangianSymplecticFamilyAutomorphism.toBase K (baseProjection K n) := by
  rw [← comparison_toBase, Iso.inv_hom_id_assoc]

/-- The original matrix coefficients are pulled from actual affine
parameter space; no scalar-extension or action premise is supplied. -/
def matrixOnLG (g : Matrix.symplecticGroup (Fin 3) Γ(affineBase K n,⊤)) :
    Matrix.symplecticGroup (Fin 3) Γ(affineLG K n,⊤) :=
  mapSymplectic Γ(affineBase K n,⊤) (parameterMap K n).appTop.hom g

/-- The actual affine-LG scheme automorphism, with its genuine inverse. -/
def automorphism (g : Matrix.symplecticGroup (Fin 3) Γ(affineBase K n,⊤)) :
    affineLG K n ≅ affineLG K n :=
  comparison K n ≪≫
    LagrangianSymplecticFamilyAutomorphism.automorphism K (baseProjection K n) g ≪≫
      (comparison K n).symm

@[reassoc] theorem automorphism_hom_parameterMap
    (g : Matrix.symplecticGroup (Fin 3) Γ(affineBase K n,⊤)) :
    (automorphism K n g).hom ≫ parameterMap K n = parameterMap K n := by
  change (comparison K n).hom ≫
    LagrangianSymplecticFamilyAutomorphism.familyMap K (baseProjection K n) g ≫
      (comparison K n).inv ≫ parameterMap K n = _
  rw [comparison_inv_toBase,
    LagrangianSymplecticFamilyAutomorphism.familyMap_toBase,comparison_toBase]

/-- The actual original LG component is the classified variable-matrix
quotient, with the literal coefficient map on global functions. -/
@[reassoc] theorem automorphism_hom_toLG
    (g : Matrix.symplecticGroup (Fin 3) Γ(affineBase K n,⊤)) :
    (automorphism K n g).hom ≫ lgProjection K n =
      actPoint K (lgProjection K n) (matrixOnLG K n g) := by
  change (comparison K n).hom ≫
    LagrangianSymplecticFamilyAutomorphism.familyMap K (baseProjection K n) g ≫
      (comparison K n).inv ≫ lgProjection K n = _
  rw [comparison_inv_toLG,
    LagrangianSymplecticFamilyAutomorphism.familyMap_toLG,actPoint_natural,comparison_toLG]
  congr 1
  apply Subtype.ext
  ext i j
  change (comparison K n).hom.appTop
      ((LagrangianSymplecticFamilyAutomorphism.toBase K (baseProjection K n)).appTop
        ((g : Matrix _ _ Γ(affineBase K n,⊤)) i j)) =
    (parameterMap K n).appTop ((g : Matrix _ _ Γ(affineBase K n,⊤)) i j)
  change ((comparison K n).hom ≫
      LagrangianSymplecticFamilyAutomorphism.toBase K (baseProjection K n)).appTop
      ((g : Matrix _ _ Γ(affineBase K n,⊤)) i j) = _
  rw [comparison_toBase]

/-- Every literal native affine coordinate is retained by this
constructed automorphism. -/
theorem automorphism_hom_coord
    (g : Matrix.symplecticGroup (Fin 3) Γ(affineBase K n,⊤)) (i : n) :
    (automorphism K n g).hom.appTop (AffineSpace.coord (space K) i) =
      AffineSpace.coord (space K) i := by
  have h := congrArg (fun f : affineLG K n ⟶ affineBase K n =>
    f.appTop (AffineSpace.coord (Spec (.of K)) i)) (automorphism_hom_parameterMap K n g)
  simpa only [Scheme.Hom.comp_appTop,CommRingCat.comp_apply,parameterMap,
    AffineSpace.map_appTop_coord] using h

@[reassoc] theorem automorphism_hom_groundProjection
    (g : Matrix.symplecticGroup (Fin 3) Γ(affineBase K n,⊤)) :
    (automorphism K n g).hom ≫ lgProjection K n ≫ projection K =
      lgProjection K n ≫ projection K := by
  rw [← AffineSpace.map_over (projection K),← Category.assoc,
    automorphism_hom_parameterMap]

end M9Native.LagrangianAffineFamilyAutomorphism

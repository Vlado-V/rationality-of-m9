module

public import M9StacksIntegration.MukaiConstantFreeBasis
public import M9StacksIntegration.MukaiCubicConstantSheaf

/-! The actual matrix of a ground-module map after associated sheaves and
structural pullback is its original matrix under the original base-ring
map. The computation retains each original basis column. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.MukaiConstantLinearCoordinates

open MukaiConstantFreeBasis MukaiCubicConstantSheaf LagrangianMatrixChart

variable (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)

def basisIso (M : ModuleCat.{u} R) (m : ℕ) (b : Basis (Fin m) R M) :
    constantObj R f M ≅ freeOn X m :=
  constantBasisIso R f M m (b.reindex Equiv.ulift.symm)

theorem basisIso_basis (M : ModuleCat.{u} R) (m : ℕ) (b : Basis (Fin m) R M) (j : Fin m) :
    (basisIso R f M m b).hom.app ⊤ (constantSection R f M (b j)) =
      freeBasisSection X m j := by
  have h := constantBasisIso_basis R f M m (b.reindex Equiv.ulift.symm) j
  simpa only [basisIso, constantSection, Basis.reindex_apply, Equiv.symm_symm,
    Equiv.ulift_apply] using h

theorem basisIso_inv_basis (M : ModuleCat.{u} R) (m : ℕ) (b : Basis (Fin m) R M)
    (j : Fin m) :
    (basisIso R f M m b).inv.app ⊤ (freeBasisSection X m j) =
      constantSection R f M (b j) := by
  have h := congrArg ((basisIso R f M m b).inv.app ⊤) (basisIso_basis R f M m b j)
  have hc := congrArg (fun a => a.app ⊤ (constantSection R f M (b j)))
    (basisIso R f M m b).hom_inv_id
  exact h.symm.trans hc

def mapInBases {M N : ModuleCat.{u} R} (a : M ⟶ N)
    (m n : ℕ) (b : Basis (Fin m) R M) (c : Basis (Fin n) R N) :
    freeOn X m ⟶ freeOn X n :=
  (basisIso R f M m b).inv ≫ constantMap R f a ≫ (basisIso R f N n c).hom

theorem mapInBases_matrix {M N : ModuleCat.{u} R} (a : M ⟶ N)
    (m n : ℕ) (b : Basis (Fin m) R M) (c : Basis (Fin n) R N) :
    Stacks.FreeSheafMatrix.toMatrix (mapInBases R f a m n b c) =
      (LinearMap.toMatrix b c a.hom).map (baseScalar R f) := by
  ext i j
  rw [← freeCoordinates_map_basis]
  change freeSectionCoordinates X n
    ((basisIso R f N n c).hom.app ⊤
      ((constantMap R f a).app ⊤
        ((basisIso R f M m b).inv.app ⊤ (freeBasisSection X m j)))) i = _
  rw [basisIso_inv_basis, constantMap_section]
  have h := constantBasisIso_coordinates R f N n (c.reindex Equiv.ulift.symm) (a.hom (b j)) i
  simpa only [basisIso, constantSection, Basis.repr_reindex_apply, Equiv.symm_symm,
    Equiv.ulift_apply, Matrix.map_apply, LinearMap.toMatrix_apply] using h

end M9Native.MukaiConstantLinearCoordinates

module

public import M9StacksIntegration.RankTwoSelectedPairSheafEntries

/-! The genuine four unit-entry basic opens cover an actual affine
frame of the rank-two target of the original epimorphism. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
universe u
namespace M9Native.RankTwoSelectedPairUnitCover
open LagrangianMatrixChart

variable (X : Scheme.{u}) [IsAffine X] {F : X.Modules}
    (φ : freeOn X 3 ⟶ F) [Epi φ] (eF : F ≅ freeOn X 2) (e : Fin 2 ↪ Fin 3)

def entry (ij : Fin 2 × Fin 2) : Γ(X,⊤) :=
  Stacks.FreeSheafMatrix.toMatrix (φ ≫ eF.hom) ij.1 (e ij.2)

def entryOpen (ij : Fin 2 × Fin 2) : X.Opens := X.basicOpen (entry X φ eF e ij)

theorem entryOpens_cover : (⨆ ij : Fin 2 × Fin 2, entryOpen X φ eF e ij) = ⊤ := by
  have h := iSup_basicOpen_of_span_eq_top (⊤ : X.Opens)
    (Set.range (entry X φ eF e))
    (RankTwoSelectedPairSheafEntries.selectedEntries_eq_top X φ eF e)
  simpa only [entryOpen, iSup_range] using h

theorem exists_mem_entryOpen (x : X) : ∃ ij : Fin 2 × Fin 2, x ∈ entryOpen X φ eF e ij := by
  have h : x ∈ (⨆ ij : Fin 2 × Fin 2, entryOpen X φ eF e ij) := by
    rw [entryOpens_cover]
    trivial
  simpa only [TopologicalSpace.Opens.mem_iSup] using h

/-- The actual retained entry is a unit in the actual open scheme's
global functions, including after restricting a nonreduced base. -/
theorem entry_isUnit (ij : Fin 2 × Fin 2) :
    IsUnit ((entryOpen X φ eF e ij).ι.appTop (entry X φ eF e ij)) := by
  let U := entryOpen X φ eF e ij
  have h := X.toRingedSpace.isUnit_res_basicOpen (entry X φ eF e ij)
  have hp : U.ι.appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op := by
    rw [Scheme.Opens.topIso_hom,Scheme.Opens.ι_appTop,← Functor.map_comp]
    congr 1
  have hq : U.ι.appTop =
      X.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op ≫ U.topIso.inv := by
    rw [← hp,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [show (entryOpen X φ eF e ij).ι.appTop = U.ι.appTop from rfl,hq]
  exact h.map U.topIso.inv.hom.toMonoidHom

end M9Native.RankTwoSelectedPairUnitCover

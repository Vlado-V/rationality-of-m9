module

public import M9StacksIntegration.RankTwoSelectedPairAlgebra
public import M9StacksIntegration.GrassmannianFixedLineSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections

/-! The unit-entry statement is attached to actual epimorphisms of
sheaves, their actual free frames, and every actual base change. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
universe u
namespace M9Native.RankTwoSelectedPairSheafEntries

open LagrangianMatrixChart Stacks.FreeSheafMatrix

variable (X : Scheme.{u})

instance free_quasicoherent (r : ℕ) : (freeOn X r).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _

/-- Exactness of actual affine sections, followed by the genuine
free-section coordinate isomorphisms, gives surjectivity of the SAME
literal matrix. -/
theorem matrix_surjective_of_epi [IsAffine X]
    (φ : freeOn X 3 ⟶ freeOn X 2) [Epi φ] :
    Function.Surjective (toMatrix φ).mulVec := by
  have hs := surjective_sectionsLinearMap_of_epi φ
  intro v
  obtain ⟨z,hz⟩ := hs ((freeSectionCoordinates X 2).symm v)
  refine ⟨freeSectionCoordinates X 3 z, ?_⟩
  rw [← GrassmannianFixedLineSheaf.map_section_coordinates]
  change φ.app ⊤ z = (freeSectionCoordinates X 2).symm v at hz
  rw [hz, LinearEquiv.apply_symm_apply]

/-- A genuine local free frame of the actual rank-two target retains
the original epimorphism and the selected pair of its original columns. -/
theorem selectedEntries_eq_top [IsAffine X] {F : X.Modules}
    (φ : freeOn X 3 ⟶ F) [Epi φ] (eF : F ≅ freeOn X 2) (e : Fin 2 ↪ Fin 3) :
    RankTwoSelectedPairAlgebra.selectedEntries Γ(X,⊤) (toMatrix (φ ≫ eF.hom)) e = ⊤ :=
  RankTwoSelectedPairAlgebra.selectedEntries_eq_top Γ(X,⊤) _
    (matrix_surjective_of_epi X (φ ≫ eF.hom)) e

/-- The same matrix after arbitrary actual scheme pullback has unit
selected-entry ideal. The test scheme need not be affine or reduced. -/
theorem selectedEntries_pullback_eq_top [IsAffine X] {F : X.Modules}
    (φ : freeOn X 3 ⟶ F) [Epi φ] (eF : F ≅ freeOn X 2) (e : Fin 2 ↪ Fin 3)
    {T : Scheme.{u}} (f : T ⟶ X) :
    RankTwoSelectedPairAlgebra.selectedEntries Γ(T,⊤)
      (toMatrix (GrassmannianFixedLineSheaf.pulledMap f (φ ≫ eF.hom))) e = ⊤ := by
  rw [GrassmannianFixedLineSheaf.pulledMap_matrix]
  exact RankTwoSelectedPairAlgebra.selectedEntries_map_eq_top Γ(X,⊤) f.appTop.hom _
    (matrix_surjective_of_epi X (φ ≫ eF.hom)) e

end M9Native.RankTwoSelectedPairSheafEntries

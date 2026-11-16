module

public import M9StacksIntegration.Sp6GaussBlockFactorization

/-!
# The natural all-ring Gauss cell of the original symplectic group

The cell is the literal unit-determinant locus of the top-left block
in the actual native matrix group. Its actual inverse extracts the
two named symmetric matrices and the actual GL3 block.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix

universe u

namespace M9Native.Sp6GaussCellFunctor

open Sp6GaussBlockFactorization

abbrev Parameters (R : Type u) [CommRing R] :=
  Symmetric3 R × Matrix.GeneralLinearGroup (Fin 3) R × Symmetric3 R

abbrev Cell (R : Type u) [CommRing R] :=
  {g : Matrix.symplecticGroup (Fin 3) R // IsUnit g.val.toBlocks₁₁.det}

variable {R : Type u} [CommRing R]

theorem blocks_mem (g : Matrix.symplecticGroup (Fin 3) R) :
    Matrix.fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂
      g.val.toBlocks₂₁ g.val.toBlocks₂₂ ∈ Matrix.symplecticGroup (Fin 3) R := by
  rw [Matrix.fromBlocks_toBlocks]
  exact g.property

def forward (p : Parameters R) : Cell R :=
  ⟨gauss p.1 p.2.1 p.2.2, by
    have hu : IsUnit p.2.1.val.det :=
      (Matrix.isUnit_iff_isUnit_det p.2.1.val).mp p.2.1.isUnit
    simpa only [gauss_blocks, Matrix.toBlocks_fromBlocks₁₁] using hu⟩

def inverseCoordinates (g : Cell R) : Parameters R :=
  (⟨g.val.val.toBlocks₂₁ * g.val.val.toBlocks₁₁⁻¹,
    lower_coordinate_symmetric _ _ _ _ (blocks_mem g.val) g.property⟩,
    Matrix.GeneralLinearGroup.mk'' g.val.val.toBlocks₁₁ g.property,
    ⟨g.val.val.toBlocks₁₁⁻¹ * g.val.val.toBlocks₁₂,
      upper_coordinate_symmetric _ _ _ _ (blocks_mem g.val) g.property⟩)

/-- The actual Gauss factorization is a genuine equivalence for
every commutative coefficient ring, including nonreduced rings. -/
def gaussEquiv : Parameters R ≃ Cell R where
  toFun := forward
  invFun := inverseCoordinates
  left_inv p := by
    rcases p with ⟨S, A, T⟩
    apply Prod.ext
    · apply Subtype.ext
      change (gauss S A T).val.toBlocks₂₁ * (gauss S A T).val.toBlocks₁₁⁻¹ = S.val
      simp only [gauss_blocks, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁]
      rw [← Matrix.GeneralLinearGroup.coe_inv]
      have hm : A.val * (A⁻¹).val = 1 := A.val_inv
      rw [Matrix.mul_assoc, hm, Matrix.mul_one]
    · apply Prod.ext
      · apply Units.ext
        change (gauss S A T).val.toBlocks₁₁ = A.val
        rw [gauss_blocks]
        rfl
      · apply Subtype.ext
        change (gauss S A T).val.toBlocks₁₁⁻¹ * (gauss S A T).val.toBlocks₁₂ = T.val
        simp only [gauss_blocks, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]
        rw [← Matrix.GeneralLinearGroup.coe_inv]
        have hm : (A⁻¹).val * A.val = 1 := A.inv_val
        rw [← Matrix.mul_assoc, hm, Matrix.one_mul]
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact (gauss_reconstruct _ _ _ _ (blocks_mem g.val) g.property).trans
      (Matrix.fromBlocks_toBlocks g.val.val)

variable {S : Type u} [CommRing S]

def mapSymmetric (ρ : R →+* S) (M : Symmetric3 R) : Symmetric3 S :=
  ⟨M.val.map ρ, by
    simpa only [Matrix.transpose_map] using
      congrArg (fun N : Mat3 R => N.map ρ) M.property⟩

def mapParameters (ρ : R →+* S) (p : Parameters R) : Parameters S :=
  (mapSymmetric ρ p.1, Matrix.GeneralLinearGroup.map ρ p.2.1, mapSymmetric ρ p.2.2)

def mapCell (ρ : R →+* S) (g : Cell R) : Cell S :=
  ⟨Sp6GroupScheme.mapMatrix ρ g.val, by
    change IsUnit (g.val.val.toBlocks₁₁.map ρ).det
    have hd : ρ g.val.val.toBlocks₁₁.det = (g.val.val.toBlocks₁₁.map ρ).det :=
      RingHom.map_det ρ g.val.val.toBlocks₁₁
    rw [← hd]
    exact g.property.map ρ⟩

theorem map_gauss (ρ : R →+* S) (p : Parameters R) :
    Sp6GroupScheme.mapMatrix ρ (gauss p.1 p.2.1 p.2.2) =
      gauss (mapParameters ρ p).1 (mapParameters ρ p).2.1 (mapParameters ρ p).2.2 := by
  apply Subtype.ext
  change (gauss p.1 p.2.1 p.2.2).val.map ρ = _
  rw [gauss_blocks, gauss_blocks]
  have hi : (p.2.1⁻¹).val.map ρ = ((Matrix.GeneralLinearGroup.map ρ p.2.1)⁻¹).val := by
    change (Matrix.GeneralLinearGroup.map ρ p.2.1⁻¹).val = _
    rw [Matrix.GeneralLinearGroup.map_inv]
  simp only [Matrix.fromBlocks_map, Matrix.map_add ρ (map_add ρ),
    Matrix.map_mul, Matrix.transpose_map, hi]
  rfl

/-- The all-ring chart equivalence is natural, so it gives a scheme
map and an actual scheme isomorphism under representability. -/
theorem gaussEquiv_natural (ρ : R →+* S) (p : Parameters R) :
    mapCell ρ (gaussEquiv p) = gaussEquiv (mapParameters ρ p) := by
  apply Subtype.ext
  exact map_gauss ρ p

theorem inverseCoordinates_natural (ρ : R →+* S) (g : Cell R) :
    inverseCoordinates (mapCell ρ g) = mapParameters ρ (inverseCoordinates g) := by
  apply gaussEquiv.injective
  change gaussEquiv (gaussEquiv.symm (mapCell ρ g)) =
    gaussEquiv (mapParameters ρ (gaussEquiv.symm g))
  rw [gaussEquiv.apply_symm_apply, ← gaussEquiv_natural, gaussEquiv.apply_symm_apply]

end M9Native.Sp6GaussCellFunctor


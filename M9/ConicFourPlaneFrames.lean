module

public import M9.ConicPencilFrames

/-!
# Actual four-plane fibers in the manuscript's matrix orientation

The four-plane is `S(F) = F S₀ Fᵀ`, with `S₀` the actual symmetric matrices
whose three diagonal entries agree. Its trace annihilator is the actual
pencil through the four columns `F dᵢ`. Thus the frozen pencil stabilizer
classification gives the RIGHT tetrahedral frame action on four-planes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace M9.ConicFourPlaneFrames

open ConicPencilFrames
open scoped BigOperators

/-- The converse trace-annihilator identity, for the literal standard
four-plane and the literal standard pencil. -/
theorem standardPencil_annihilator (Q : Conic) :
    Q ∈ standardPencil ↔ ∀ A ∈ standardFourPlane, tracePair A Q = 0 := by
  constructor
  · intro hQ A hA
    exact (standardFourPlane_annihilator A).mp hA Q hQ
  · intro h
    have h0 := h (standardFourPlaneCoordinates.symm (Pi.single 0 1)).val
      (standardFourPlaneCoordinates.symm (Pi.single 0 1)).property
    have h1 := h (standardFourPlaneCoordinates.symm (Pi.single 1 1)).val
      (standardFourPlaneCoordinates.symm (Pi.single 1 1)).property
    have h2 := h (standardFourPlaneCoordinates.symm (Pi.single 2 1)).val
      (standardFourPlaneCoordinates.symm (Pi.single 2 1)).property
    have h3 := h (standardFourPlaneCoordinates.symm (Pi.single 3 1)).val
      (standardFourPlaneCoordinates.symm (Pi.single 3 1)).property
    have h10 : Q.val 1 0 = Q.val 0 1 := congrFun (congrFun Q.property 0) 1
    have h20 : Q.val 2 0 = Q.val 0 2 := congrFun (congrFun Q.property 0) 2
    have h21 : Q.val 2 1 = Q.val 1 2 := congrFun (congrFun Q.property 1) 2
    norm_num [tracePair, standardFourPlaneCoordinates, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Pi.single_apply, h10, h20, h21] at h0 h1 h2 h3
    have h01 : Q.val 0 1 = 0 := h1
    have h02 : Q.val 0 2 = 0 := h2
    have h12 : Q.val 1 2 = 0 := h3
    apply (conic_in_standardPencil_iff Q).mpr
    intro i
    fin_cases i <;>
      norm_num [quadraticValue_coordinates, TetrahedralGroup.diagonal,
        TetrahedralGroup.diagonalQ, h01, h02, h12] <;>
      linear_combination h0

/-- Transpose as an actual invertible matrix, keeping the original
`GL₃` convention. -/
def transposeGL (F : GL3) : GL3 := FrameAction.contragredient F⁻¹

@[simp] theorem transposeGL_val (F : GL3) :
    (transposeGL F : Mat3) = (F : Mat3).transpose := by
  change (↑(F⁻¹)⁻¹ : Mat3).transpose = (F : Mat3).transpose
  rw [inv_inv]

@[simp] theorem transposeGL_inv (F : GL3) :
    transposeGL F⁻¹ = (transposeGL F)⁻¹ := by simp [transposeGL]

/-- Congruence on symmetric matrices, in the manuscript's order. -/
def conicPush (F : GL3) : Conic ≃ₗ[ℂ] Conic := conicPullback (transposeGL F)

@[simp] theorem conicPush_val (F : GL3) (A : Conic) :
    (conicPush F A).val = (F : Mat3) * A.val * (F : Mat3).transpose := by
  simp [conicPush, conicPullback_val]

@[simp] theorem conicPush_inv_apply (F : GL3) (A : Conic) :
    conicPush F⁻¹ (conicPush F A) = A := by
  simp only [conicPush, transposeGL_inv, conicPullback_inv_apply]

@[simp] theorem conicPush_apply_inv (F : GL3) (A : Conic) :
    conicPush F (conicPush F⁻¹ A) = A := by
  simpa only [inv_inv] using conicPush_inv_apply F⁻¹ A

/-- The actual four-plane `F S₀ Fᵀ`. -/
def fourPlane (F : GL3) : Submodule ℂ Conic :=
  standardFourPlane.map (conicPush F).toLinearMap

theorem mem_fourPlane (F : GL3) (A : Conic) :
    A ∈ fourPlane F ↔ conicPush F⁻¹ A ∈ standardFourPlane := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    simpa using hB
  · intro hA
    exact ⟨conicPush F⁻¹ A, hA, conicPush_apply_inv F A⟩

theorem tracePair_push_pull (F : GL3) (A Q : Conic) :
    tracePair (conicPush F A) Q = tracePair A (conicPullback F Q) := by
  simp only [tracePair, conicPush_val, conicPullback_val]
  calc
    _ = Matrix.trace ((F : Mat3) * (A.val * (F : Mat3).transpose * Q.val)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((A.val * (F : Mat3).transpose * Q.val) * (F : Mat3)) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The actual four-plane is the trace annihilator of its actual framed
pencil. This uses the original covariant congruence orientation. -/
theorem fourPlane_annihilator (F : GL3) (A : Conic) :
    A ∈ fourPlane F ↔ ∀ Q ∈ framedPencil F, tracePair A Q = 0 := by
  rw [mem_fourPlane, standardFourPlane_annihilator]
  constructor
  · intro h Q hQ
    have hp := (mem_pencilThrough_transformed F Q).mp hQ
    have hh := h (conicPullback F Q) hp
    simpa only [tracePair_push_pull, conicPullback_inv_apply] using hh
  · intro h Q hQ
    rw [tracePair_push_pull]
    apply h
    apply (mem_pencilThrough_transformed F _).mpr
    simpa only [conicPullback_apply_inv] using hQ

/-- Conversely the actual pencil is recovered from the actual
four-plane, with no generic-position or fiber-cardinality premise. -/
theorem framedPencil_annihilator (F : GL3) (Q : Conic) :
    Q ∈ framedPencil F ↔ ∀ A ∈ fourPlane F, tracePair A Q = 0 := by
  change Q ∈ pencilThrough _ ↔ _
  rw [mem_pencilThrough_transformed, standardPencil_annihilator]
  constructor
  · intro h A hA
    obtain ⟨B, hB, rfl⟩ := hA
    change tracePair (conicPush F B) Q = 0
    rw [tracePair_push_pull]
    exact h B hB
  · intro h A hA
    have hh := h (conicPush F A) ⟨A, hA, rfl⟩
    simpa only [tracePair_push_pull] using hh

theorem fourPlane_eq_iff_framedPencil_eq (F F' : GL3) :
    fourPlane F = fourPlane F' ↔ framedPencil F = framedPencil F' := by
  constructor
  · intro h
    ext Q
    simp only [framedPencil_annihilator, h]
  · intro h
    ext A
    simp only [fourPlane_annihilator, h]

/-- The literal closed-complex frame classification, with RIGHT `Γ`:
`S(F)=S(F')` exactly when `F'=c F γ`. -/
theorem fourPlane_fiber_iff (F F' : GL3) :
    fourPlane F = fourPlane F' ↔
      ∃ g : TetrahedralGroup.Gamma, ∃ c : ℂ,
        c ≠ 0 ∧ (F' : Mat3) = c • ((F : Mat3) * TetrahedralGroup.matrix g) := by
  rw [fourPlane_eq_iff_framedPencil_eq, eq_comm, framedPencil_fiber_iff]
  constructor
  · rintro ⟨g, c, hc, h⟩
    refine ⟨g, c, hc, ?_⟩
    have hh := congrArg (fun M : Mat3 => (F : Mat3) * M) h
    simpa [Units.val_mul, Matrix.mul_assoc] using hh
  · rintro ⟨g, c, hc, h⟩
    refine ⟨g, c, hc, ?_⟩
    change (↑F⁻¹ : Mat3) * (F' : Mat3) = c • TetrahedralGroup.matrix g
    rw [h]
    simp

@[simp] theorem gammaMatrix_mul_inv (g h : TetrahedralGroup.Gamma) :
    TetrahedralGroup.matrix (g * h⁻¹) =
      TetrahedralGroup.matrix g * (↑(FrameAction.tetrahedralGL h)⁻¹ : Mat3) := by
  change (FrameAction.tetrahedralGL (g * h⁻¹) : Mat3) = _
  rw [map_mul, map_inv, Units.val_mul]
  rfl

/-- The right action of the actual tetrahedral group on projective
invertible frames is free. No fiber count is used. -/
theorem rightGamma_projectively_free (F : GL3) (g h : TetrahedralGroup.Gamma) (c : ℂ)
    (he : (F : Mat3) * TetrahedralGroup.matrix g =
      c • ((F : Mat3) * TetrahedralGroup.matrix h)) : g = h := by
  have hs : TetrahedralGroup.matrix (g * h⁻¹) = c • (1 : Mat3) := by
    have hh := congrArg (fun M : Mat3 =>
      (↑F⁻¹ : Mat3) * M * (↑(FrameAction.tetrahedralGL h)⁻¹ : Mat3)) he
    simpa [gammaMatrix_mul_inv, Matrix.mul_assoc,
      show TetrahedralGroup.matrix h = (FrameAction.tetrahedralGL h : Mat3) from rfl] using hh
  exact mul_inv_eq_one.mp (TetrahedralGroup.scalar_eq_one (g * h⁻¹) c hs)

/-- The open frame condition used to normalize every tetrahedral right
translate in the `F₀₀ = 1` chart. -/
def FirstRowNonzero (F : GL3) : Prop := ∀ j, (F : Mat3) 0 j ≠ 0

theorem firstRowNonzero_of_normalized (F : GL3) (h00 : (F : Mat3) 0 0 = 1)
    (h01 : (F : Mat3) 0 1 ≠ 0) (h02 : (F : Mat3) 0 2 ≠ 0) : FirstRowNonzero F := by
  intro j
  fin_cases j
  · change (F : Mat3) 0 0 ≠ 0
    rw [h00]
    exact one_ne_zero
  · change (F : Mat3) 0 1 ≠ 0
    exact h01
  · change (F : Mat3) 0 2 ≠ 0
    exact h02

/-- Multiplication on the right by an actual signed permutation
preserves nonvanishing of all entries of the first row. -/
theorem firstRowNonzero_rightGamma (F : GL3) (hF : FirstRowNonzero F)
    (g : TetrahedralGroup.Gamma) : FirstRowNonzero (F * FrameAction.tetrahedralGL g) := by
  intro j
  change ((F : Mat3) * TetrahedralGroup.matrix g) 0 j ≠ 0
  obtain ⟨σ, ε, hg⟩ := TetrahedralGroup.matrix_isSignedPermutation g
  have he : ((F : Mat3) * TetrahedralGroup.matrix g) 0 j =
      (F : Mat3) 0 (σ.symm j) * (if ε (σ.symm j) then -1 else 1) := by
    rw [hg, Matrix.mul_apply, Finset.sum_eq_single (σ.symm j)]
    · simp [TetrahedralGroup.signedMatrix]
    · intro i _ hi
      have hne : j ≠ σ i := by
        intro hji
        exact hi (σ.injective (hji.symm.trans (σ.apply_symm_apply j).symm))
      simp [TetrahedralGroup.signedMatrix, hne]
    · simp
  rw [he]
  apply mul_ne_zero (hF _)
  cases ε (σ.symm j) <;> norm_num

/-- An actual invertible scalar matrix. -/
def scalarGL (c : ℂ) (hc : c ≠ 0) : GL3 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (c • (1 : Mat3)) (by
    simpa [Matrix.det_smul] using pow_ne_zero 3 hc)

/-- The actual normalization of a frame by its nonzero `(0,0)` entry. -/
def normalizeFrame (F : GL3) (hF : (F : Mat3) 0 0 ≠ 0) : GL3 :=
  scalarGL ((F : Mat3) 0 0)⁻¹ (inv_ne_zero hF) * F

@[simp] theorem normalizeFrame_val (F : GL3) (hF : (F : Mat3) 0 0 ≠ 0) :
    (normalizeFrame F hF : Mat3) = ((F : Mat3) 0 0)⁻¹ • (F : Mat3) := by
  change (((F : Mat3) 0 0)⁻¹ • (1 : Mat3)) * (F : Mat3) = _
  simp

/-- Every actual tetrahedral right translate has a well-defined
normalized frame in the same affine chart. -/
def normalizedRightFrame (F : GL3) (hF : FirstRowNonzero F)
    (g : TetrahedralGroup.Gamma) : GL3 :=
  normalizeFrame (F * FrameAction.tetrahedralGL g) (firstRowNonzero_rightGamma F hF g 0)

@[simp] theorem normalizedRightFrame_val (F : GL3) (hF : FirstRowNonzero F)
    (g : TetrahedralGroup.Gamma) :
    (normalizedRightFrame F hF g : Mat3) =
      (((F : Mat3) * TetrahedralGroup.matrix g) 0 0)⁻¹ •
        ((F : Mat3) * TetrahedralGroup.matrix g) := by
  simp only [normalizedRightFrame, normalizeFrame_val, Units.val_mul]
  rfl

theorem normalizedRightFrame_zero_zero (F : GL3) (hF : FirstRowNonzero F)
    (g : TetrahedralGroup.Gamma) : (normalizedRightFrame F hF g : Mat3) 0 0 = 1 := by
  have h0 : ((F : Mat3) * TetrahedralGroup.matrix g) 0 0 ≠ 0 :=
    firstRowNonzero_rightGamma F hF g 0
  simp [normalizedRightFrame_val, h0]

theorem normalizedRightFrame_firstRowNonzero (F : GL3) (hF : FirstRowNonzero F)
    (g : TetrahedralGroup.Gamma) : FirstRowNonzero (normalizedRightFrame F hF g) := by
  intro j
  have h0 : ((F : Mat3) * TetrahedralGroup.matrix g) 0 0 ≠ 0 :=
    firstRowNonzero_rightGamma F hF g 0
  have hj : ((F : Mat3) * TetrahedralGroup.matrix g) 0 j ≠ 0 :=
    firstRowNonzero_rightGamma F hF g j
  rw [normalizedRightFrame_val]
  exact mul_ne_zero (inv_ne_zero h0) hj

theorem normalizedRightFrame_fourPlane (F : GL3) (hF : FirstRowNonzero F)
    (g : TetrahedralGroup.Gamma) : fourPlane F = fourPlane (normalizedRightFrame F hF g) := by
  apply (fourPlane_fiber_iff F _).mpr
  exact ⟨g, _, inv_ne_zero (firstRowNonzero_rightGamma F hF g 0),
    normalizedRightFrame_val F hF g⟩

/-- The actual closed-complex fiber in the normalized first-row chart. -/
def NormalizedFiber (F : GL3) :=
  {F' : GL3 // (F' : Mat3) 0 0 = 1 ∧ FirstRowNonzero F' ∧ fourPlane F = fourPlane F'}

def rightFiberPoint (F : GL3) (hF : FirstRowNonzero F)
    (g : TetrahedralGroup.Gamma) : NormalizedFiber F :=
  ⟨normalizedRightFrame F hF g, normalizedRightFrame_zero_zero F hF g,
    normalizedRightFrame_firstRowNonzero F hF g, normalizedRightFrame_fourPlane F hF g⟩

theorem rightFiberPoint_injective (F : GL3) (hF : FirstRowNonzero F) :
    Function.Injective (rightFiberPoint F hF) := by
  intro g h heq
  have he := congrArg (fun x : NormalizedFiber F => (x.val : Mat3)) heq
  change (normalizedRightFrame F hF g : Mat3) = (normalizedRightFrame F hF h : Mat3) at he
  rw [normalizedRightFrame_val, normalizedRightFrame_val] at he
  let cg := (((F : Mat3) * TetrahedralGroup.matrix g) 0 0)⁻¹
  let ch := (((F : Mat3) * TetrahedralGroup.matrix h) 0 0)⁻¹
  have hcg : cg ≠ 0 := inv_ne_zero (firstRowNonzero_rightGamma F hF g 0)
  change cg • ((F : Mat3) * TetrahedralGroup.matrix g) =
    ch • ((F : Mat3) * TetrahedralGroup.matrix h) at he
  apply rightGamma_projectively_free F g h (cg⁻¹ * ch)
  have hh := congrArg (fun M : Mat3 => cg⁻¹ • M) he
  simpa only [smul_smul, inv_mul_cancel₀ hcg, one_smul] using hh

theorem rightFiberPoint_surjective (F : GL3) (hF : FirstRowNonzero F) :
    Function.Surjective (rightFiberPoint F hF) := by
  intro N
  obtain ⟨g, c, hc, hN⟩ := (fourPlane_fiber_iff F N.val).mp N.property.2.2
  have h0 : ((F : Mat3) * TetrahedralGroup.matrix g) 0 0 ≠ 0 :=
    firstRowNonzero_rightGamma F hF g 0
  have he00 : 1 = c * ((F : Mat3) * TetrahedralGroup.matrix g) 0 0 := by
    have hh := congrArg (fun M : Mat3 => M 0 0) hN
    simpa only [N.property.1, Matrix.smul_apply, smul_eq_mul] using hh
  have hc' : c = (((F : Mat3) * TetrahedralGroup.matrix g) 0 0)⁻¹ := by
    apply mul_right_cancel₀ h0
    exact he00.symm.trans (inv_mul_cancel₀ h0).symm
  refine ⟨g, Subtype.ext (Units.ext ?_)⟩
  change (normalizedRightFrame F hF g : Mat3) = (N.val : Mat3)
  rw [normalizedRightFrame_val, ← hc']
  exact hN.symm

/-- The actual normalized closed-complex fiber is bijective to the
actual tetrahedral group, rather than assumed to have twenty-four points. -/
def normalizedFiberEquiv (F : GL3) (hF : FirstRowNonzero F) :
    TetrahedralGroup.Gamma ≃ NormalizedFiber F :=
  Equiv.ofBijective (rightFiberPoint F hF)
    ⟨rightFiberPoint_injective F hF, rightFiberPoint_surjective F hF⟩

theorem nat_card_normalizedFiber (F : GL3) (hF : FirstRowNonzero F) :
    Nat.card (NormalizedFiber F) = 24 := by
  simpa only [Nat.card_eq_fintype_card, TetrahedralGroup.card_gamma] using
    (Nat.card_congr (normalizedFiberEquiv F hF)).symm

end M9.ConicFourPlaneFrames

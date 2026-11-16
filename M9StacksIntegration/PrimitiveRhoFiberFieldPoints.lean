module

public import M9StacksIntegration.PrimitiveRhoFiberNondegenerate
public import M9StacksIntegration.PrimitiveExtensionFieldBridge
public import M9StacksIntegration.RadicalOrthogonalComplement

/-! The actual nondegenerate rho-family over every complex extension field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module AlgebraicGeometry CategoryTheory
open scoped Classical TensorProduct Matrix

namespace M9Native.PrimitiveRhoFiberFieldPoints
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveRadicalScheme
open PrimitiveRhoFiberChart PrimitiveRhoFiberNondegenerate PrimitiveExtensionFieldBridge

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

/-- The fixed native coordinates describe the original primitive wedge pairing over K. -/
theorem coordinates_pairing (u v : Primitive K) :
    primitivePairing K u v =
      (pairingMatrix.map (algebraMap ℂ K)).toBilin' (fieldCoordinates K u) (fieldCoordinates K v) := by
  let e := scalarPrimitiveEquiv K
  have h := scalarPrimitiveEquiv_pairing K (e.symm u) (e.symm v)
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,
    scalarExtendedPairing_coordinates] at h
  have hc (w : Primitive K) : PrimitiveRadicalNativeScheme.scalarExtendedCoordinates K (e.symm w) =
      fieldCoordinates K w := by
    rw [← scalarPrimitiveEquiv_coordinates]
    exact congrArg (fieldCoordinates K) (e.apply_symm_apply w)
  rw [hc,hc] at h
  exact h

/-- The actual lifted four-frame in the original exterior kernel over K. -/
def mixedFrame (P : Matrix (Fin 12) (Fin 4) K) : (Fin 4 → K) →ₗ[K] Primitive K :=
  (fieldCoordinates K).symm.toLinearMap.comp
    (Matrix.toLin' (liftMatrix.map (algebraMap ℂ K) * P))

theorem mixedFrame_coordinates (P : Matrix (Fin 12) (Fin 4) K) (x : Fin 4 → K) :
    fieldCoordinates K (mixedFrame K P x) = (liftMatrix.map (algebraMap ℂ K) * P) *ᵥ x := by
  simp only [mixedFrame,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    Matrix.toLin'_apply]

theorem mixedFrame_gram (P : Matrix (Fin 12) (Fin 4) K) :
    LinearMap.BilinForm.toMatrix' ((primitivePairing K).compl₁₂ (mixedFrame K P) (mixedFrame K P)) =
      gramMatrix K P := by
  have hB : (primitivePairing K).compl₁₂ (mixedFrame K P) (mixedFrame K P) =
      (pairingMatrix.map (algebraMap ℂ K)).toBilin'.compl₁₂
        (Matrix.toLin' (liftMatrix.map (algebraMap ℂ K) * P))
        (Matrix.toLin' (liftMatrix.map (algebraMap ℂ K) * P)) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [LinearMap.compl₁₂_apply,coordinates_pairing,mixedFrame_coordinates,mixedFrame_coordinates]
    rfl
  rw [hB]
  change LinearMap.BilinForm.toMatrix'
    ((pairingMatrix.map (algebraMap ℂ K)).toBilin'.comp
      (Matrix.toLin' (liftMatrix.map (algebraMap ℂ K) * P))
      (Matrix.toLin' (liftMatrix.map (algebraMap ℂ K) * P))) = gramMatrix K P
  rw [LinearMap.BilinForm.toMatrix'_comp,LinearMap.toMatrix'_toLin',
    LinearMap.BilinForm.toMatrix'_toBilin']
  rfl

theorem mixedFrame_pullback_nondegenerate (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) :
    ((primitivePairing K).compl₁₂ (mixedFrame K P) (mixedFrame K P)).Nondegenerate := by
  have h := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' (gramMatrix K P) hP
  rw [← mixedFrame_gram K P,Matrix.toBilin'_toMatrix'] at h
  exact h

section Range
variable {V : Type*} [AddCommGroup V] [Module K V]

omit [Algebra ℂ K] in
/-- Pullback nondegeneracy proves actual frame independence. -/
theorem injective_of_pullback_nondegenerate (B : LinearMap.BilinForm K V)
    (f : (Fin 4 → K) →ₗ[K] V) (hf : (B.compl₁₂ f f).Nondegenerate) : Function.Injective f := by
  intro x y h
  have hxy : f (x-y) = 0 := by rw [map_sub,h,sub_self]
  have hz : x-y = 0 := by
    apply hf.1
    intro z
    change B (f (x-y)) (f z) = 0
    rw [hxy,map_zero,LinearMap.zero_apply]
  exact sub_eq_zero.mp hz

omit [Algebra ℂ K] in
/-- Pullback nondegeneracy gives nondegeneracy on the actual image subspace. -/
theorem restrict_range_nondegenerate (B : LinearMap.BilinForm K V)
    (f : (Fin 4 → K) →ₗ[K] V) (hf : (B.compl₁₂ f f).Nondegenerate) :
    (B.restrict f.range).Nondegenerate := by
  constructor
  · intro x hx
    obtain ⟨a,ha⟩ := x.property
    have hz : a = 0 := by
      apply hf.1
      intro b
      have h := hx ⟨f b,⟨b,rfl⟩⟩
      change B x.val (f b) = 0 at h
      change B (f a) (f b) = 0
      simpa only [ha] using h
    apply Subtype.ext
    simpa only [hz,map_zero,Submodule.coe_zero] using ha.symm
  · intro x hx
    obtain ⟨a,ha⟩ := x.property
    have hz : a = 0 := by
      apply hf.2
      intro b
      have h := hx ⟨f b,⟨b,rfl⟩⟩
      change B (f b) x.val = 0 at h
      change B (f b) (f a) = 0
      simpa only [ha] using h
    apply Subtype.ext
    simpa only [hz,map_zero,Submodule.coe_zero] using ha.symm

end Range

def mixedPlane (P : Matrix (Fin 12) (Fin 4) K) : Submodule K (Primitive K) := (mixedFrame K P).range

theorem mixedPlane_finrank (P : Matrix (Fin 12) (Fin 4) K) (hP : (gramMatrix K P).det ≠ 0) :
    finrank K (mixedPlane K P) = 4 := by
  let e := LinearEquiv.ofInjective (mixedFrame K P)
    (injective_of_pullback_nondegenerate K _ _ (mixedFrame_pullback_nondegenerate K P hP))
  have h := e.finrank_eq
  simpa [mixedPlane] using h.symm

theorem mixedPlane_nondegenerate (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) :
    ((primitivePairing K).restrict (mixedPlane K P)).Nondegenerate :=
  restrict_range_nondegenerate K _ _ (mixedFrame_pullback_nondegenerate K P hP)

/-- The original mixed-section columns are orthogonal to the actual original rho. -/
theorem lift_pairing_rho_zero : liftMatrix.transpose * pairingMatrix * rhoColumn = 0 := by
  ext i j
  rw [Matrix.mul_assoc]
  change liftMatrix.col i ⬝ᵥ (pairingMatrix *ᵥ coordinateRho) = 0
  rw [← Matrix.mulVec_single_one liftMatrix i,liftMatrix,LinearMap.toMatrix'_mulVec,
    ← Matrix.toBilin'_apply',pairingMatrix,Matrix.toBilin'_toMatrix']
  change primitivePairing ℂ
    (primitiveCoordinates.symm (coordinateLift (Pi.single i 1)))
    (primitiveCoordinates.symm coordinateRho) = 0
  simp only [coordinateLift,coordinateRho,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [primitivePairing_neg_swap]
  have h := mixedLift_mem_perp (Pi.single i 1)
  have hz := h (rho ℂ) (Submodule.mem_span_singleton_self _)
  rw [hz,neg_zero]

/-- Rho is orthogonal to the actual mixed four-plane over every extension field. -/
theorem rho_orthogonal_mixedPlane (P : Matrix (Fin 12) (Fin 4) K) :
    rho K ∈ (primitivePairing K).orthogonal (mixedPlane K P) := by
  have hm := congrArg (fun M : Matrix (Fin 12) (Fin 1) ℂ => M.map (algebraMap ℂ K))
    lift_pairing_rho_zero
  simp only [Matrix.map_mul,Matrix.map_zero,map_zero] at hm
  change (liftMatrix.map (algebraMap ℂ K)).transpose * pairingMatrix.map (algebraMap ℂ K) *
    rhoColumn.map (algebraMap ℂ K) = 0 at hm
  have hz : (liftMatrix.map (algebraMap ℂ K)).transpose *ᵥ
      (pairingMatrix.map (algebraMap ℂ K) *ᵥ (fun i => algebraMap ℂ K (coordinateRho i))) = 0 := by
    rw [Matrix.mulVec_mulVec]
    funext i
    change ((liftMatrix.map (algebraMap ℂ K)).transpose * pairingMatrix.map (algebraMap ℂ K) *
      rhoColumn.map (algebraMap ℂ K)) i (0 : Fin 1) = 0
    exact congrFun (congrFun hm i) 0
  intro v hv
  obtain ⟨x,rfl⟩ := hv
  rw [coordinates_pairing,mixedFrame_coordinates,fieldCoordinates_rho]
  rw [Matrix.toBilin'_apply',← Matrix.mulVec_mulVec,dotProduct_comm,
    ← Matrix.dotProduct_transpose_mulVec]
  change (P *ᵥ x) ⬝ᵥ ((liftMatrix.map (algebraMap ℂ K)).transpose *ᵥ
    (pairingMatrix.map (algebraMap ℂ K) *ᵥ (fun i => algebraMap ℂ K (coordinateRho i)))) = 0
  rw [hz,dotProduct_zero]

def orthogonalPlane (P : Matrix (Fin 12) (Fin 4) K) : Submodule K (Primitive K) :=
  (primitivePairing K).orthogonal (rhoLine K ⊔ mixedPlane K P)

/-- Dimension and radical of the output nine-plane follow from the actual Gram determinant. -/
theorem orthogonalPlane_finrank_radical (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) :
    finrank K (orthogonalPlane K P) = 9 ∧
      M9.RadicalFiber.radical (primitivePairing K) (orthogonalPlane K P) = rhoLine K := by
  exact M9.RadicalFiber.finrank_nine_and_radical_orthogonal_line_sup
    (primitivePairing K) (primitivePairing_isAlt K) (primitivePairing_nondegenerate K)
    (finrank_primitive K) (rho K) (rho_ne_zero K) (mixedPlane K P)
    (mixedPlane_finrank K P hP) (mixedPlane_nondegenerate K P hP) (rho_orthogonal_mixedPlane K P)

def fiveFrame (P : Matrix (Fin 12) (Fin 4) K) : (Fin 5 → K) →ₗ[K] Primitive K :=
  (fieldCoordinates K).symm.toLinearMap.comp (Matrix.toLin' (frame K P))

theorem fiveFrame_coordinates (P : Matrix (Fin 12) (Fin 4) K) (x : Fin 5 → K) :
    fieldCoordinates K (fiveFrame K P x) = frame K P *ᵥ x := by
  simp only [fiveFrame,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    Matrix.toLin'_apply]

theorem fiveFrame_single (P : Matrix (Fin 12) (Fin 4) K) (j : Fin 1 ⊕ Fin 4) :
    fiveFrame K P (Pi.single (finSumFinEquiv j) 1) =
      Sum.elim (fun _ => rho K) (fun a => mixedFrame K P (Pi.single a 1)) j := by
  apply (fieldCoordinates K).injective
  rw [fiveFrame_coordinates]
  rcases j with i | a
  · simp only [Sum.elim_inl]
    rw [Matrix.mulVec_single_one,fieldCoordinates_rho]
    funext k
    simp only [Matrix.col_apply,frame,Matrix.submatrix_apply,id_eq,Equiv.symm_apply_apply,
      sumFrame,Matrix.fromCols_apply_inl,Matrix.map_apply,rhoColumn,coordinateRho]
  · simp only [Sum.elim_inr]
    rw [Matrix.mulVec_single_one,mixedFrame_coordinates,Matrix.mulVec_single_one]
    funext k
    simp only [Matrix.col_apply,frame,Matrix.submatrix_apply,id_eq,Equiv.symm_apply_apply,
      sumFrame,Matrix.fromCols_apply_inr]

omit [Algebra ℂ K] in
/-- The actual image of a finite free frame is spanned by its literal basis images. -/
theorem range_eq_span_singles {V : Type*} [AddCommGroup V] [Module K V]
    (n : ℕ) (f : (Fin n → K) →ₗ[K] V) :
    f.range = Submodule.span K (Set.range (fun i => f (Pi.single i 1))) := by
  have h := (Pi.basisFun K (Fin n)).constr_range K (f := fun i => f ((Pi.basisFun K (Fin n)) i))
  rw [Module.Basis.constr_self] at h
  simpa only [Pi.basisFun_apply] using h

theorem fiveFrame_range (P : Matrix (Fin 12) (Fin 4) K) :
    (fiveFrame K P).range = rhoLine K ⊔ mixedPlane K P := by
  apply le_antisymm
  · rw [range_eq_span_singles K]
    apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5).surjective j
    change fiveFrame K P (Pi.single (finSumFinEquiv j) 1) ∈ rhoLine K ⊔ mixedPlane K P
    rw [fiveFrame_single]
    rcases j with i | a
    · exact (le_sup_left : rhoLine K ≤ rhoLine K ⊔ mixedPlane K P)
        (Submodule.mem_span_singleton_self _)
    · exact (le_sup_right : mixedPlane K P ≤ rhoLine K ⊔ mixedPlane K P) ⟨Pi.single a 1,rfl⟩
  · apply sup_le
    · apply (Submodule.span_singleton_le_iff_mem (rho K) (fiveFrame K P).range).mpr
      refine ⟨Pi.single ((finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5) (.inl (0 : Fin 1))) 1,?_⟩
      exact fiveFrame_single K P (.inl 0)
    · rw [mixedPlane,range_eq_span_singles K]
      apply Submodule.span_le.mpr
      rintro v ⟨a,rfl⟩
      refine ⟨Pi.single ((finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5) (.inr a)) 1,?_⟩
      exact fiveFrame_single K P (.inr a)

/-- The literal native quotient kernel, realized in the original primitive exterior space over K. -/
def quotientKernel (P : Matrix (Fin 12) (Fin 4) K) : Submodule K (Primitive K) :=
  (Matrix.toLin' (quotientMatrix K P)).ker.map (fieldCoordinates K).symm.toLinearMap

theorem quotientKernel_eq_orthogonal (P : Matrix (Fin 12) (Fin 4) K) :
    quotientKernel K P = (primitivePairing K).orthogonal (fiveFrame K P).range := by
  ext v
  rw [quotientKernel,Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm]
  rw [quotientMatrix,matrix_kernel_orthogonal]
  constructor
  · intro h w hw
    obtain ⟨x,rfl⟩ := hw
    rw [coordinates_pairing,fiveFrame_coordinates]
    exact h _ ⟨x,rfl⟩
  · intro h w hw
    obtain ⟨x,rfl⟩ := hw
    have hv := h (fiveFrame K P x) ⟨x,rfl⟩
    rw [coordinates_pairing,fiveFrame_coordinates] at hv
    exact hv

theorem quotientKernel_eq_orthogonalPlane (P : Matrix (Fin 12) (Fin 4) K) :
    quotientKernel K P = orthogonalPlane K P := by
  rw [quotientKernel_eq_orthogonal,fiveFrame_range]
  rfl

/-- Every literal quotient kernel on the Gram nondegenerate locus has the required actual radical. -/
theorem quotientKernel_finrank_radical (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) :
    finrank K (quotientKernel K P) = 9 ∧
      M9.RadicalFiber.radical (primitivePairing K) (quotientKernel K P) = rhoLine K := by
  rw [quotientKernel_eq_orthogonalPlane]
  exact orthogonalPlane_finrank_radical K P hP

/-- The native nondegenerate localization discharges the determinant condition at every field point. -/
theorem fieldPoint_kernel_finrank_radical (f : nondegenerateRing →ₐ[ℂ] K) :
    finrank K (quotientKernel K (localizedGraph.map f)) = 9 ∧
      M9.RadicalFiber.radical (primitivePairing K) (quotientKernel K (localizedGraph.map f)) = rhoLine K :=
  quotientKernel_finrank_radical K _ (fieldPoint_gram_det_ne_zero f)

end M9Native.PrimitiveRhoFiberFieldPoints

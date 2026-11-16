module

public import M9StacksIntegration.ReducedGraphCenter

/-! The full actual SL3 semidirect C2 action restricts to the native cubic-center
fixed field. Its transport uses only the proved actual determinant quotient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace M9Native.ReducedGraphTwistedAction

open ReducedGraphAction ReducedGraphCenter
open M9.PrimitiveProjectiveStabilizer

abbrev H := Stabilizer ℂ
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) ℂ
abbrev FF := ReducedGraphCenter.FF
abbrev NativeField := ReducedGraphCenter.NativeField
abbrev Roots := ReducedGraphCenter.Roots

def centralSLHom : Roots →* SL3 where
  toFun a := M9.PrimitiveRepresentation.centralElement ℂ (a.val : ℂ) (root_cube a)
  map_one' := by
    apply Subtype.ext
    simp [M9.PrimitiveRepresentation.centralElement]
  map_mul' a b := by
    apply Subtype.ext
    simp [M9.PrimitiveRepresentation.centralElement, smul_smul, mul_comm]

def centerHom : Roots →* H := SemidirectProduct.inl.comp centralSLHom

theorem centerHom_apply (a : Roots) : centerHom a = centralElement a := rfl

theorem centralSL_commute (a : Roots) (g : SL3) : centralSLHom a * g = g * centralSLHom a := by
  apply Subtype.ext
  change ((a.val : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * g.val =
    g.val * ((a.val : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem inverseTranspose_center (a : Roots) :
    M9.PrimitiveRepresentation.inverseTranspose ℂ (centralSLHom a) = centralSLHom a⁻¹ := by
  rw [M9.PrimitiveRepresentation.inverseTranspose, ← map_inv centralSLHom]
  apply Subtype.ext
  change ((((a⁻¹).val : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).transpose) =
    ((a⁻¹).val : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
  rw [Matrix.transpose_smul, Matrix.transpose_one]

theorem inverseTransposeAction_center (c : M9.CentralSignQuotient.C2) (a : Roots) :
    ∃ b : Roots, inverseTransposeAction ℂ c (centralSLHom b) = centralSLHom a := by
  rcases M9.CentralSignQuotient.c2_cases c with rfl | rfl
  · refine ⟨a, ?_⟩
    rw [map_one]
    rfl
  · refine ⟨a⁻¹, ?_⟩
    rw [inverseTransposeAction_epsilon]
    change M9.PrimitiveRepresentation.inverseTranspose ℂ (centralSLHom a⁻¹) = centralSLHom a
    rw [inverseTranspose_center, inv_inv]

/-- The actual cubic center is normalized by every actual stabilizer element. -/
theorem center_mul (a : Roots) (w : H) : ∃ b : Roots, centerHom a * w = w * centerHom b := by
  obtain ⟨b, hb⟩ := inverseTransposeAction_center w.right a
  refine ⟨b, ?_⟩
  apply SemidirectProduct.ext
  · change centralSLHom a * w.left = w.left * inverseTransposeAction ℂ w.right (centralSLHom b)
    rw [hb]
    exact centralSL_commute a w.left
  · change 1 * w.right = w.right * 1
    simp

theorem nativeCentral_preserved (w : H) (z : NativeField) (hz : z ∈ nativeCentralFixedField) :
    nativeFieldRepresentation ℂ w z ∈ nativeCentralFixedField := by
  rw [mem_nativeCentralFixedField_iff] at hz ⊢
  intro a
  obtain ⟨b, hb⟩ := center_mul a w
  change nativeFieldRepresentation ℂ (centerHom a) (nativeFieldRepresentation ℂ w z) = _
  rw [← AlgEquiv.mul_apply, ← map_mul, hb, map_mul, AlgEquiv.mul_apply]
  exact congrArg (nativeFieldRepresentation ℂ w) (hz b)

/-- Literal restriction of the full actual native stabilizer representation. -/
def centralRestriction (w : H) : nativeCentralFixedField ≃ₐ[ℂ] nativeCentralFixedField where
  toFun z := ⟨nativeFieldRepresentation ℂ w z.val, nativeCentral_preserved w z.val z.property⟩
  invFun z := ⟨nativeFieldRepresentation ℂ w⁻¹ z.val, nativeCentral_preserved w⁻¹ z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    change nativeFieldRepresentation ℂ w⁻¹ (nativeFieldRepresentation ℂ w z.val) = z.val
    rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv z := by
    apply Subtype.ext
    change nativeFieldRepresentation ℂ w (nativeFieldRepresentation ℂ w⁻¹ z.val) = z.val
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_mul' z v := Subtype.ext (map_mul (nativeFieldRepresentation ℂ w) z.val v.val)
  map_add' z v := Subtype.ext (map_add (nativeFieldRepresentation ℂ w) z.val v.val)
  commutes' c := Subtype.ext ((nativeFieldRepresentation ℂ w).commutes c)

def centralRepresentation : H →* (nativeCentralFixedField ≃ₐ[ℂ] nativeCentralFixedField) where
  toFun := centralRestriction
  map_one' := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    change nativeFieldRepresentation ℂ 1 z.val = z.val
    rw [map_one]
    rfl
  map_mul' w v := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    change nativeFieldRepresentation ℂ (w * v) z.val =
      nativeFieldRepresentation ℂ w (nativeFieldRepresentation ℂ v z.val)
    rw [map_mul]
    rfl

/-- Actual action on determinant-twisted generic coordinates, obtained from
its genuine native central fixed-field quotient. The group remains SL3 semidirect C2. -/
def twistedFieldRepresentation : H →* (FF ≃ₐ[ℂ] FF) :=
  (AlgEquiv.autCongr nativeDeterminantQuotient.symm).toMonoidHom.comp centralRepresentation

theorem twistedFieldRepresentation_quotient (w : H) (z : FF) :
    (nativeDeterminantQuotient (twistedFieldRepresentation w z)).val =
      nativeFieldRepresentation ℂ w (nativeDeterminantQuotient z).val := by
  change (nativeDeterminantQuotient
    (nativeDeterminantQuotient.symm (centralRestriction w (nativeDeterminantQuotient z)))).val = _
  exact congrArg Subtype.val
    (nativeDeterminantQuotient.apply_symm_apply (centralRestriction w (nativeDeterminantQuotient z)))

theorem mem_fixedField_range_iff {k L G : Type*} [Field k] [Field L] [Algebra k L]
    [Group G] (ρ : G →* (L ≃ₐ[k] L)) (z : L) :
    z ∈ IntermediateField.fixedField ρ.range ↔ ∀ w : G, ρ w z = z := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h w
    exact h (ρ w) ⟨w, rfl⟩
  · rintro h σ ⟨w, rfl⟩
    exact h w

/-- Full actual stabilizer invariants of the original native Gr4(12) field. -/
def nativeHFixedField : IntermediateField ℂ NativeField :=
  IntermediateField.fixedField (nativeFieldRepresentation ℂ).range

/-- Full actual stabilizer invariants after the genuine determinant quotient. -/
def twistedHFixedField : IntermediateField ℂ FF :=
  IntermediateField.fixedField twistedFieldRepresentation.range

theorem mem_nativeHFixedField_iff (z : NativeField) : z ∈ nativeHFixedField ↔
    ∀ w : H, nativeFieldRepresentation ℂ w z = z := mem_fixedField_range_iff _ _

theorem mem_twistedHFixedField_iff (z : FF) : z ∈ twistedHFixedField ↔
    ∀ w : H, twistedFieldRepresentation w z = z := mem_fixedField_range_iff _ _

def fullToCentral : nativeHFixedField →ₐ[ℂ] nativeCentralFixedField where
  toFun z := ⟨z.val, (mem_nativeCentralFixedField_iff z.val).mpr (fun a =>
    (mem_nativeHFixedField_iff z.val).mp z.property (centralElement a))⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

def toTwistedAux : nativeHFixedField →ₐ[ℂ] FF :=
  nativeDeterminantQuotient.symm.toAlgHom.comp fullToCentral

theorem toTwistedAux_fixed (z : nativeHFixedField) : toTwistedAux z ∈ twistedHFixedField := by
  apply (mem_twistedHFixedField_iff _).mpr
  intro w
  apply nativeDeterminantQuotient.injective
  apply Subtype.ext
  have hq : nativeDeterminantQuotient (toTwistedAux z) = fullToCentral z :=
    nativeDeterminantQuotient.apply_symm_apply (fullToCentral z)
  rw [twistedFieldRepresentation_quotient, hq]
  exact (mem_nativeHFixedField_iff z.val).mp z.property w

def toTwistedFixed : nativeHFixedField →ₐ[ℂ] twistedHFixedField where
  toFun z := ⟨toTwistedAux z, toTwistedAux_fixed z⟩
  map_zero' := Subtype.ext (map_zero toTwistedAux)
  map_one' := Subtype.ext (map_one toTwistedAux)
  map_add' z v := Subtype.ext (map_add toTwistedAux z v)
  map_mul' z v := Subtype.ext (map_mul toTwistedAux z v)
  commutes' c := Subtype.ext (toTwistedAux.commutes c)

theorem toTwistedFixed_surjective : Function.Surjective toTwistedFixed := by
  intro y
  have hy : (nativeDeterminantQuotient y.val).val ∈ nativeHFixedField := by
    apply (mem_nativeHFixedField_iff _).mpr
    intro w
    rw [← twistedFieldRepresentation_quotient]
    exact congrArg (fun z : FF => (nativeDeterminantQuotient z).val)
      ((mem_twistedHFixedField_iff y.val).mp y.property w)
  let x : nativeHFixedField := ⟨(nativeDeterminantQuotient y.val).val, hy⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change nativeDeterminantQuotient.symm (fullToCentral x) = y.val
  have hx : fullToCentral x = nativeDeterminantQuotient y.val := Subtype.ext rfl
  rw [hx, AlgEquiv.symm_apply_apply]

/-- The original full native stabilizer fixed field is exactly the full fixed
field of the actual determinant-twisted graph action. -/
def nativeFullFixedEquiv : nativeHFixedField ≃ₐ[ℂ] twistedHFixedField :=
  AlgEquiv.ofBijective toTwistedFixed ⟨toTwistedFixed.injective, toTwistedFixed_surjective⟩

theorem nativeFullFixedEquiv_quotient (z : nativeHFixedField) :
    (nativeDeterminantQuotient (nativeFullFixedEquiv z).val).val = z.val :=
  congrArg Subtype.val (nativeDeterminantQuotient.apply_symm_apply (fullToCentral z))

end M9Native.ReducedGraphTwistedAction
